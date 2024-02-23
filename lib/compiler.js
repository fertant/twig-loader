var path = require("path");
var fs = require("fs");
var yaml = require('yaml');
var hashGenerator = require("hasha");
var _ = require("underscore");
var mapcache = require("./mapcache");

module.exports = function(options) {
    return function(id, tokens, pathToTwig) {
        var includes = [];
        var resourcePath = mapcache.get(id);

        var readData = function (pathToData) {
            try {
                if (fs.statSync(pathToData).isFile()) {
                    const ymlData = fs.readFileSync(pathToData, 'utf8')
                    return yaml.parse(ymlData);
                }
            } catch (error) {
                return [];
            }            
        }
        var data = readData(resourcePath.replace('.twig', '.yml'));
        var dataPointer = []
        dataPointer = JSON.parse(JSON.stringify(data));

        var setPointer = function (token) {
            _.each(token.expression, function(expression) {
              if (expression.type === 'Twig.expression.type.variable' && expression.value in data) {
                dataPointer = JSON.parse(JSON.stringify(data[expression.value]));
              } else if (expression.type === 'Twig.expression.type.key.period' && expression.key in dataPointer) {
                dataPointer = dataPointer[expression.key];
              } else if (expression.type === 'Twig.expression.type.slice') {
                dataPointer = dataPointer.slice(expression.params[0] ?? 0, expression.params[1] ?? dataPointer.length);
              }
            })            
        }

        var parseDynamicString = function (token) {
            switch(token.type) {
                case 'Twig.expression.type.string':
                    if (!dataPointer['left']) {
                        dataPointer['left'] = token.value;
                    } else {
                        dataPointer['right'] = token.value;
                    }
                    break;
                case 'Twig.expression.type.variable':
                    dataPointer['expression_variable'] = dataPointer[token.value];
                    break;
                case 'Twig.expression.type.key.period':
                    if (
                        dataPointer['expression_variable'][token.key] !== null &&
                        typeof dataPointer['expression_variable'][token.key] !== 'object' &&
                        !Array.isArray(dataPointer['expression_variable'][token.key])
                    ) {
                        if (!dataPointer['left']) {
                            dataPointer['left'] = dataPointer['expression_variable'][token.key];
                        } else {
                            dataPointer['right'] = dataPointer['expression_variable'][token.key];
                        }
                    } else {
                        dataPointer['expression_variable'] = dataPointer['expression_variable'][token.key];
                    }
                    break;
                case 'Twig.expression.type.operator.binary':
                    if (token.associativity === 'leftToRight' && token.operator === '~') {
                        if (dataPointer['left'] && dataPointer['right']) {
                            dataPointer['expression_parse'] += dataPointer['left'] + dataPointer['right'];
                        } else if (dataPointer['left']) {
                            dataPointer['expression_parse'] += dataPointer['left']
                        }
                        delete dataPointer['expression_variable'];
                        delete dataPointer['left'];
                        delete dataPointer['right'];
                    }
                    break;
            }
        }

        var discoverTwig = function(namespace) {
            if (!fs.existsSync(namespace)) return;
            fs.readdirSync(namespace).forEach(file => {
                const pathToFile = path.join(namespace, file);
                if (fs.statSync(pathToFile).isDirectory()) {
                    return discoverTwig(pathToFile);
                } else if (pathToFile.includes('.twig') && !includes.includes(pathToFile)) {
                    return includes.push(pathToFile);
                }
            });
        }

        var processPathAlias = function(token) {
            if (options.twigOptions && options.twigOptions.namespaces) {
                var namespaces = options.twigOptions.namespaces;
                Object.keys(namespaces).forEach( ns => {
                    var colon = new RegExp('^' + ns + '::');
                    var atSign = new RegExp('^@' + ns);

                    if (colon.test(token.value)) {
                        token.value = token.value.replace(ns + '::', namespaces[ns]);
                    } else if (atSign.test(token.value)) {
                        token.value = token.value.replace('@' + ns, namespaces[ns]);
                    }
                });
            }
            
        };
        var processDependency = function(token) {
            processPathAlias(token);
            includes.push(token.value);
            token.value = hashGenerator(path.resolve(path.dirname(resourcePath), token.value));
        };

        var processToken = function(token) {
            if (token.type == "logic" && token.token.type) {
                switch(token.token.type) {
                    case 'Twig.logic.type.for':
                        setPointer(token.token);
                        if (
                            token.token.valueVar && 
                            token.token.valueVar !== null && 
                            0 in dataPointer
                        ) {
                            dataPointer[token.token.valueVar] = dataPointer[0];
                        }
                        _.each(token.token.output, processToken);
                        break;
                    case 'Twig.logic.type.block':
                    case 'Twig.logic.type.if':
                    case 'Twig.logic.type.elseif':
                    case 'Twig.logic.type.else':
                    case 'Twig.logic.type.spaceless':
                    case 'Twig.logic.type.setcapture':
                    case 'Twig.logic.type.macro':
                        _.each(token.token.output, processToken);
                        break;
                    case 'Twig.logic.type.extends':
                    case 'Twig.logic.type.include':
                        if (
                            token.token.stack.every(function (token) {
                                return (
                                    token.type === "Twig.expression.type.string"
                                );
                            })
                        ) {
                            _.each(token.token.stack, processDependency);
                        } else {
                            dataPointer['expression_parse'] = '';
                            _.each(token.token.stack, parseDynamicString);
                            token.token.stack = [{
                              type: "Twig.expression.type.string",
                              value: dataPointer['expression_parse'],
                            }];
                            _.each(token.token.stack, processDependency);
                        }
                        break;
                    case 'Twig.logic.type.embed':
                        _.each(token.token.output, processToken);
                        _.each(token.token.stack, processDependency);
                        break;
                    case 'Twig.logic.type.import':
                    case 'Twig.logic.type.from':
                        if (token.token.expression != '_self') {
                            _.each(token.token.stack, processDependency);
                        }
                        break;
                }
            }
        };

        var parsedTokens = JSON.parse(tokens);

        _.each(parsedTokens, processToken);

        var opts = Object.assign({}, options.twigOptions, {
            id: id,
            data: parsedTokens,
            allowInlineIncludes: true,
            rethrow: true,
        });
        var output = [
            'var twig = require("' + pathToTwig + '").twig,',
            '    template = twig(' + JSON.stringify(opts) + ');\n',
            'module.exports = function(context) { return template.render(context); }'
        ];

        if (includes.length > 0) {
            _.each(_.uniq(includes), function(file) {
                output.unshift("require("+ JSON.stringify(file) +");\n");
            });
        }

        return output.join('\n');
    };
};

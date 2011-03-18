/*jshint bitwise: true, curly: true, eqeqeq: true, forin: true, immed: false, laxbreak: false, 
		 newcap: true, noarg: true, nonew: true, nomen: false, onevar: true, plusplus: false, 
		 undef: true, sub: false, strict: true, white: false, passfail: false  */

/*global AnExpectedGlobal: true, AGlobalNotToOverwritten: false,
		 netscape: true, FileIO: true, DirIO: true, parse: true,
		JSAST: true, Narcissus: true */


JSAST = (function () {
	"use strict";
	
	var _asASTString, _outputElement, _outputNode, // Resolves co-recursive forward refs
		INDENTATION = "    ",
		WORKING_DIR = "/Users/m3rabb/Dev/Maude/k-framework/examples/inProgress/kJS/",
		IDS_FILE_NAME = "js-json-ast-ids.k",
		PARSER = Narcissus.parser,
		NODE = PARSER.Node,
		DEFINITIONS = Narcissus.definitions,
		TOKENS = DEFINITIONS.tokens,
		OP_TYPE_NAMES = DEFINITIONS.opTypeNames,
		EXCLUDED_PROPERTIES = 
			['type', 'target', 'tokenizer', 'exports', 'labels',
			 'modAssns', 'modDecls', 'modDefns', 'modLoads'],
		IDS_FILE_PREFIX = "kmod JS-JSON-AST-IDS\n" + 
			"    is including PL-INT + PL-FLOAT + PL-STRING + PL-ID\n\n" +
			"    syntax JSJsonAstIds ::= \n\t\t",
		IDS_FILE_SUFFIX = "\nendkm\n",
		IDS_FILE_PREFIX_LENGTH = IDS_FILE_PREFIX.length,
		IDS_FILE_SUFFIX_LENGTH = IDS_FILE_SUFFIX.length,
		_indentLevel = 0, _indentations = [""],
		_allIds = {},
		_collectIds;
	
	function _addIds(ids) {
		ids.forEach(function (id) {_allIds[id] = true;});
	}
	
	function _includeIds() {
		return Object.keys(_allIds).sort();
	}
	
	function _indent(startLevel_) {
		var indent;
		_indentLevel = (startLevel_ === undefined) ? _indentLevel + 1 : startLevel_;
		indent = _indentations[_indentLevel];
		if (indent === undefined) {
			indent = _indentations[_indentLevel] = INDENTATION.repeat(_indentLevel);
		}
		return indent;
	}

	function _outdent() {
		return _indentations[--_indentLevel];
	}
	
	function _isAllowedProperty(propertyName) {
		return EXCLUDED_PROPERTIES.indexOf(propertyName) === -1;
	}
	
	function _tokenName(string) {
        var token = TOKENS[string];
        return (/^\W/).test(token) ? OP_TYPE_NAMES[token] : token.toUpperCase();
    }
   
	function _outputArray(elements) {
		var output, indent;
		if (elements.length === 0) {return "[]";}
		output = "[";
		indent = _indent();
		elements.forEach(function (element) {
			output += "\n" + indent + _outputElement(element) + ",";
		});
		output = output.slice(0, -1) + "\n" + _outdent() + "]";
		return output;
	}
	
	_outputElement = function _outputElement(element) {
		if (element instanceof NODE) {return _outputNode(element);}
		if (Array.isArray(element)) {return _outputArray(element);}
		if (typeof element === 'string') {return element.quote();}
		if (element instanceof RegExp) {return element.toString().quote();}
		return "" + element;
	};
		
	_outputNode = function _outputNode(node) {
		var keys = Object.keys(node),
			ids = keys.filter(_isAllowedProperty),
			indent = _indent(),
			output = "{\n",
			typeName = _tokenName(node.type).quote();
			
		if (_collectIds) {_addIds(ids);}
		output += indent + "type : " + typeName;
		ids.sort();
		ids.forEach(function (id) {
			output += ",\n" + indent + id + " : ";
			output += _outputElement(node[id]);
		});
		output += "\n" + _outdent() + "}";
		return output;
    };

	NODE.prototype.toString = function () {
		return _indent(0) + _outputNode(this);
	};
	
	function _updateIds() {
		var path = WORKING_DIR + "syntax/" + IDS_FILE_NAME, 
			idsFile = FileIO.open(path),
			delimiter = " |\n\t\t",
			input, ids, output;
		if (! idsFile.exists()) {return "ERROR: " + IDS_FILE_NAME + " doesn't exist!";}
		
		input = FileIO.read(idsFile);
		input = input.slice(IDS_FILE_PREFIX_LENGTH, -IDS_FILE_SUFFIX_LENGTH);
		ids = input.split(delimiter);
		_addIds(ids);
		ids = _includeIds();
		output = IDS_FILE_PREFIX + ids.join(delimiter) + IDS_FILE_SUFFIX;
		return FileIO.write(idsFile, output);
	}
	
	return {
		generate : function generate(fileNameWithExt, collectIds_) {
			var dirName = WORKING_DIR + "examples/",
				fileName = fileNameWithExt.replace(/\.js$/, ""),
				path = dirName + fileName,
				// isStrictMode = isStrictMode_ || false,
				sourceFile, source, ast, json, jsonFile, maude, maudeFile, resultFlag;
	
			netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");		
			if (fileNameWithExt.search(/\.js$/) === -1) {return "ERROR: Must be a .js file!";}
			sourceFile = FileIO.open(path + ".js");
			if (! sourceFile.exists()) {return "ERROR " + fileNameWithExt + " doesn't exist!";}
			
			_collectIds = collectIds_ || false;
			source = FileIO.read(sourceFile);
			ast = PARSER.parse(source);
			json = ast.toString();
			
			jsonFile = FileIO.open(path + ".json");
			resultFlag = FileIO.write(jsonFile, json);
			if (_collectIds) {resultFlag = resultFlag && _updateIds();}
			
			// maude = "red \n" + json + "\n .\n"
			// maudeFile = FileIO.open(path + ".maude");
			// resultFlag = resultFlag && FileIO.write(maudeFile, maude);
			return resultFlag;
		}
	};
})();
	
	
/*

	function _outputTerminal(substrings, element) {
		switch (typeof element) {
			case 'object' :
				if (element === null) {
					substrings.push("null");
				} else {
					substrings.push("$", element);
				}
				break;
			case 'undefined' :
				substrings.push("undefined");
				break;
			case 'string' :
				substrings.push('"', element.replace(/\"/g, "\\\""), '"');
				break;
			default :
				substrings.push(element);
		}
	}

	function _outputPrefixes(levels) {
		var count = levels.length, 
			output = [], 
			index, isLastElement;
		for (index = 0; index < count; index += 1) {
			isLastElement = levels[index];
			output.push(isLastElement ? "    " : "|   ");
		}
		return output;
	}

	function _outputElement(lines, element, levels) {
		var currentLine;
		if (Array.isArray(element)) {
			_asASTString(element, lines, levels);
		} else {
			currentLine = lines.pop();
			currentLine.push("--> ");
			_outputTerminal(currentLine, element);
			lines.push(currentLine.join(""));
		}
	}

	_asASTString = function _asASTString(elements, lines, levels) {
		var index = 0,
			count = elements.length,
			match = count - 1,
			isLastElement = count <= 1,
			currentLine = lines.pop(),
			element;
		
		currentLine.push("--(");
		if (count === 0) {
			currentLine.push(")");
			lines.push(currentLine.join(""));
			return;
		}
	
		currentLine.push(isLastElement ? ")" : "-");
		do {
			lines.push(currentLine);
			levels.push(isLastElement);
			element = elements[index];
			_outputElement(lines, element, levels);
			levels.pop();
			if (isLastElement) {return;}
			isLastElement = (++index === match);
			currentLine = _outputPrefixes(levels);
			currentLine.push(isLastElement ? ")-" : "|-");
		} while (true);
	};

	function _normalizedOutput(lines) {
		var output = [],
			maxLength = 0,
			length, count;
		
		lines.forEach(function (line) {
			length = line.length;
			if (length > maxLength) {maxLength = length;}
		});
		lines.forEach(function (line) {
			output.push(line);
			count = maxLength - line.length;
			while (count-- > 0) {output.push(" ");}
			output.push("    \\", "\n");
		});
		output.pop();
		output.push("\"");
		output = output.join("");
		return output;
	}

	function _asSExpression(elements, separator, substrings) {
		var element, 
			index = 0, 
			count = elements.length;
	
		substrings.push( "(" );
		if (count > 0) {
			do {
				element = elements[index];
				if (Array.isArray(element)) {
					_asSExpression(element, separator, substrings);
				} else {
					_outputTerminal(substrings, element);
				}
				if (++index >= count) {break;}
				substrings.push(separator);
			} while (true);
		}
		substrings.push( ")" );
	}
	
	Array.prototype.asDiagram = function asDiagram() {
		var lines = ["\"", [" -"]];
		_asASTString(this, lines, [true]);
		lines.push("");
		return _normalizedOutput(lines);
	};

	Array.prototype.asSExpression = function asSExpression(separator_) {
		var separator = separator_ || ", ",
			substrings = [];
		_asSExpression(this, separator, substrings);
		return substrings.join("");
	};
	
	
	return {
		generate : function generate(fileNameWithExt, isStrictMode_) {
			var dirName = "/Users/m3rabb/Dev/Maude/k-framework/examples/inProgress/kJS/examples/",
				fileName = fileNameWithExt.replace(/\.js$/, ""),
				path = dirName + fileName,
				isStrictMode = isStrictMode_ || false,
				sourceFile, source, ast, sexp, diagram, tree, json,
				sexpFile, diagramFile, jsonFile, resultFlag;
	
			netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
			
			if (fileNameWithExt.search(/\.js$/) === -1) {return "ERROR: Must be a .js file!";}
			
			sourceFile = FileIO.open(path + ".js");
			if (! sourceFile.exists()) {return "ERROR " + fileNameWithExt + " doesn't exist!";}
	
			source = FileIO.read(sourceFile);
			ast = parse(source, isStrictMode, true);
			sexp = ast.asSExpression(",,");
			diagram = ast.asDiagram();
			tree = Narcissus.parser.parse(source);
			json = tree.toString();
		
			sexpFile = FileIO.open(path + ".sexp");
			diagramFile = FileIO.open(path + ".diagram");
			jsonFile = FileIO.open(path + ".json");
			resultFlag = FileIO.write(sexpFile, sexp);
			resultFlag = resultFlag && FileIO.write(diagramFile, diagram);
			resultFlag = resultFlag && FileIO.write(jsonFile, json);
			// resultFlag = resultFlag && FileIO.unlink(sexpFile);
			// resultFlag = resultFlag && FileIO.unlink(diagramFile);
			return resultFlag;
		}
	};
	*/

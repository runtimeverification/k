/*jshint bitwise: true, curly: true, eqeqeq: true, forin: true, immed: false, laxbreak: false, 
		 newcap: true, noarg: true, nonew: true, nomen: false, onevar: true, plusplus: false, 
		 undef: true, sub: false, strict: true, white: false, passfail: true  */

/*global AnExpectedGlobal: true, AGlobalNotToOverwritten: false,
		 netscape: true, FileIO: true, DirIO: true, parse: true,
		JSAST: true */


JSAST = (function () {
	"use strict";
	
	var _outputTerminal, _outputPrefixes, _outputElement, 
		_asASTString, _normalizedOutput, _asSExpression;

	_outputTerminal = function _outputTerminal(substrings, element) {
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
	};

	_outputPrefixes = function _outputPrefixes(levels) {
		var count = levels.length, 
			output = [], 
			index, isLastElement;
		for (index = 0; index < count; index += 1) {
			isLastElement = levels[index];
			output.push(isLastElement ? "    " : "|   ");
		}
		return output;
	};

	_outputElement = function _outputElement(lines, element, levels) {
		var currentLine;
		if (Array.isArray(element)) {
			_asASTString(element, lines, levels);
		} else {
			currentLine = lines.pop();
			currentLine.push("--> ");
			_outputTerminal(currentLine, element);
			lines.push(currentLine.join(""));
		}
	};

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

	_normalizedOutput = function _normalizedOutput(lines) {
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
	};

	_asSExpression = function _asSExpression(elements, separator, substrings) {
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
	};
	
	Array.prototype.asDiagram = function asDiagram() {
		var lines = ["\"", [" -"]];
		_asASTString(this, lines, [true]);
		lines.push("");
		return _normalizedOutput(lines);
	};

	Array.prototype.asSExpression = function asSExpression(options_) {
		var separator = (options_ && options_.separator) || ", ",
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
				sourceFile, source, ast, sexp, diagram,
				sexpFile, diagramFile, sexpFlag, resultFlag;
	
			netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
			
			if (fileNameWithExt.search(/\.js$/) === -1) {return "ERROR: Must be a .js file!";}
			
			sourceFile = FileIO.open(path + ".js");
			if (! sourceFile.exists()) {return "ERROR " + fileNameWithExt + " doesn't exist!";}
	
			source = FileIO.read(sourceFile);
			ast = parse(source, isStrictMode, true);
			sexp = ast.asSExpression();
			diagram = ast.asDiagram();
	
			sexpFile = FileIO.open(path + ".sexp");
			diagramFile = FileIO.open(path + ".diagram");
			resultFlag = FileIO.write(sexpFile, sexp);
			resultFlag = resultFlag && FileIO.write(diagramFile, diagram);
			// resultFlag = resultFlag && FileIO.unlink(sexpFile);
			// resultFlag = resultFlag && FileIO.unlink(diagramFile);
			return resultFlag;
		}
	};
})();

/*
// Example use:
// var fileIn = FileIO.open('/test.txt');
// if (fileIn.exists()) {
// 	var fileOut = FileIO.open('/copy of test.txt');
// 	var str = FileIO.read(fileIn);
// 	var rv = FileIO.write(fileOut, str);
// 	alert('File write: ' + rv);
// 	rv = FileIO.write(fileOut, str, 'a');
// 	alert('File append: ' + rv);
// 	rv = FileIO.unlink(fileOut);
// 	alert('File unlink: ' + rv);
// }

myStuff = function () {
	netscape.security.PrivilegeManager.enablePrivilege("UniversalXPConnect");
	var dir = '/Users/m3rabb/Dev/JavaScript/Hot Sausage/examples/';
	var fileName = 'that';
	var extension = '.txt';
	var path = dir + fileName + extension; 
	var myCC = Components.classes;
	var fileIn = FileIO.open(path);
	var size = fileIn.fileSize();
	if (fileIn.exists()) {
		var fileOut = FileIO.open(dir + fileName + '2' + extension);
		var str = FileIO.read(fileIn);
		var rv = FileIO.write(fileOut, str);
		alert('File write: ' + rv);
		rv = FileIO.write(fileOut, str, 'a');
		alert('File append: ' + rv);
		rv = FileIO.unlink(fileOut);
		alert('File unlink: ' + rv);
	}
};
*/


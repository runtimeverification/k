/**
 * So, you think you know JavaScript?
 * @see		http://dmitry.baranovskiy.com/post/so-you-think-you-know-javascript 
 * @see 	http://www.nczonline.net/blog/2010/01/26/answering-baranovskiys-javascript-quiz/
 *
 */

var	window = this;	// In web browsers, at the global level this === window. However to remove 
					// dependency from the DOM we set it explicitly to allow the following tests 
					// to be used without modification.

var _answers = [];

var alert = function alert(content) {
	_answers.push(content);
}; // Intercept the builtin alert function.

var identicalAnswerPair = function identicalAnswerPair() {
	return _answers[0] === _answers[1];
};

var lastAnswer = function lastAnswer() {return _answers[0];};

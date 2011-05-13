/**
 * So, you think you know JavaScript?
 * @see		http://dmitry.baranovskiy.com/post/so-you-think-you-know-javascript 
 * @see 	http://www.nczonline.net/blog/2010/01/26/answering-baranovskiys-javascript-quiz/
 *
 */


// Example 3
function a(x) {
    return x * 2;
}
var a;
alert(a);

// Function declarations trump variable declarations unless there’s an initialization. 
// There’s no initialization here, so the alert displays the source code of the function.

alert("function a(x) {
    return x * 2;
}");

Riot.run(function () {
	context("Baranovskiy's 'So, you think you know JavaScript?'", function () {
		asserts("Example 3", identicalAnswerPair()).isTrue();
	});
}




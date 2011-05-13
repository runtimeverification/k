/**
 * So, you think you know JavaScript?
 * @see		http://dmitry.baranovskiy.com/post/so-you-think-you-know-javascript 
 * @see 	http://www.nczonline.net/blog/2010/01/26/answering-baranovskiys-javascript-quiz/
 *
 */

							
// Example 1
if (!("a" in window)) { 
    var a = 1;
}
alert(a);

// Equivalent reordering 
var aa;
if (!("aa" in window)) {
    aa = 1;
}
alert(aa);

Riot.run(function () {
	context("Baranovskiy's 'So, you think you know JavaScript?'", function () {
		asserts("Example 1", identicalAnswerPair()).isTrue();
	});
}

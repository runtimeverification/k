/**
 * So, you think you know JavaScript?
 * @see		http://dmitry.baranovskiy.com/post/so-you-think-you-know-javascript 
 * @see 	http://www.nczonline.net/blog/2010/01/26/answering-baranovskiys-javascript-quiz/
 *
 */


// Example 2
var a = 1,
b = function a(x) {
    x && a(--x);
};
alert(a);

// Equivalent reordering 
var aa = 1,
    bb = function(x) {
        x && bb(--x);
    };
alert(aa);

Riot.run(function () {
	context("Baranovskiy's 'So, you think you know JavaScript?'", function () {
		asserts("Example 2", identicalAnswerPair()).isTrue();
	});
}

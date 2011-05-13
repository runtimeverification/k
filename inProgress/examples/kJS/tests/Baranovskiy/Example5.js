/**
 * So, you think you know JavaScript?
 * @see		http://dmitry.baranovskiy.com/post/so-you-think-you-know-javascript 
 * @see 	http://www.nczonline.net/blog/2010/01/26/answering-baranovskiys-javascript-quiz/
 *
 */


// Example 5
function a() {
    alert(this);
}
a.call(null);


Riot.run(function () {
	context("Baranovskiy's 'So, you think you know JavaScript?'", function () {
		asserts("Example 5", lastAnswer() === window).isTrue();
	});
}


/*
ECMA-262, 3rd edition describes what should happen when null is passed in as the first argument 
to call():

If thisArg is null or undefined, the called function is passed the global object as the this value. 
Otherwise, the called function is passed ToObject(thisArg) as the this value.

So whenever null is passed to call() (or its sibling, apply()), it defaults to the global object, 
which is window. Given that, the example code can be rewritten in a more understandable way as:

function a() {
    alert(this);
}
a.call(window);

This code makes it obvious that the alert will be displaying the string equivalent of the window 
object.
*/



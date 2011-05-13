/**
 * So, you think you know JavaScript?
 * @see		http://dmitry.baranovskiy.com/post/so-you-think-you-know-javascript 
 * @see 	http://www.nczonline.net/blog/2010/01/26/answering-baranovskiys-javascript-quiz/
 *
 */


// Example 4
function b(x, y, a) {
    arguments[2] = 10;
    alert(a);
}
b(1, 2, 3);


Riot.run(function () {
	context("Baranovskiy's 'So, you think you know JavaScript?'", function () {
		asserts("Example 4", lastAnswer() === 10).isTrue();
	});
}

/*
ECMA-262, 3rd Edition, section 10.1.8 says about an arguments object:

For each non-negative integer, arg, less than the value of the length property, a property is 
created with name ToString(arg) and property attributes { DontEnum }. The initial value of this 
property is the value of the corresponding actual parameter supplied by the caller. The first 
actual parameter value corresponds to arg = 0, the second to arg = 1, and so on. In the case when 
arg is less than the number of formal parameters for the Function object, this property shares its 
value with the corresponding property of the activation object. This means that changing this 
property changes the corresponding property of the activation object and vice versa.

In short, each entry in the arguments object is a duplicate of each named argument. Note that the 
values are shared, but not the memory space. The two memory spaces are kept synchronized by the 
JavaScript engine, which means that both arguments[2] and a contain the same value at all times. 
That value ends up being 10.
*/


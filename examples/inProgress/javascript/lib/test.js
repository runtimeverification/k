
// var source = "		\
// 	var x, y = 0;	\
// 	switch (x) {	\
// 		case 0 : 	\
// 			y = "xyz";\
// 			break;	\
// 		case 1 : 	\
// 		case 2 : 	\
// 			y += 1;	\
// 			break;	\
// 		default : 	\
// 			y = 100;\
// 	}				\
// 	y -= 20;		\
// ";

var source = "		\
	var x, y = 0;	\
	switch (x) {	\
		case 0 : y = 'xyz'; \
		break; 		\
	}				\
";

var tree = this.narcissus.jsparse(source);
var s= tree.toString();

var ajax = new XMLHttpRequest();
xml.open('POST', 'writefile', true);
ajax.setRequestHeader('Content-Type', 'application/x-www-form-urlencoded');

if (ajax.overrideMimeType) ajax.setRequestHeader('Connection', 'close');
ajax.send( serialize( data ) );
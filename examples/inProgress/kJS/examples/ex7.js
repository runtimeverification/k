// switch (x) {
// 	case 'number' : true;
// }

// switch (typeof element) {
// 	case 'number' :
// 		x = 2;
// 		break;
// }


var x = 0;
switch (typeof element) {
	case 'object' :
	case 'number' :
		x = 2;
	case 'undefined' :
		x = 11,22,33;
		break;
	default :
		x = 1;
		break;
	case 'string' :
		x = '"'.replace(/\"/g, "\\\"");
		break;
}

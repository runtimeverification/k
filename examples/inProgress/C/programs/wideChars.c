#include <stdio.h>
#include <wchar.h>
#include <wctype.h>
int main(void){
	wchar_t myChar1 = L'Ω';
	wchar_t myChar2 = 0x2126;  // hexadecimal encoding of char Ω using UTF-16
	wchar_t myString1[] = L"♠♣♥♦";
	wchar_t myString2[] = { 0x2660, 0x2661, 0x2662, 0x2663, 0x0000 }; // hex encoding of null-terminated string ♠♣♥♦ using UTF-16
	 
	printf("This is a long string: %ls \n",myString1);
	wprintf(L"This is a long string: %s \n",myString2);
	return 0;
}

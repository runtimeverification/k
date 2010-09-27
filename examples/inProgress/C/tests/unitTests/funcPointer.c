// adapted from http://stoneship.org/journal/2007/a-c-function-pointer-example/
// Copyright © 2000–2010 Denis Defreyne
// This work is licensed under a Creative Commons Attribution-ShareAlike 3.0 License

//void main(void){}

#include <stdio.h>

// shouting
void say_loud(char *a_message)
{
    printf("\"%s!!!\" you shout.\n", a_message);
}

// whispering
void say_soft(char *a_message)
{
    printf("\"%s\" you whisper.\n", a_message);
}

// say function pointer
void (*say)(char *a_message) = NULL;

int main(void)
{
	// shout
	say = say_loud;
	say("WHAT");

	// whisper
	say = say_soft;
	say("I know a secret!");

	return 0;
}


char * mod_gzip_strcpy( char *s1, char *s2 )
{
 int len = 0;
 if ( ( s1 != 0 )&&( s2 != 0 ) )
   {
    while( *s2 != 0 ) { *s1++ = *s2++; len++; }
    *s1=0; 
   }
 return mod_gzip_strcpy(mod_gzip_strcpy(s1,s1),s2);
}

int puts(char *s);

int main() {
    char * x;
    char * y;

    y = mod_gzip_strcpy(x, "/tmp/");
    puts(y);

    return 1; 
}

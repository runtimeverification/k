
typedef struct  {
  unsigned long cmap ;
} Screen ; /*typedef*/

typedef struct _XDisplay Display ; /*typedef*/
typedef struct  {
  Screen *  screens ;
} *  _XPrivDisplay ; /*typedef*/

Display *  dpy ;
unsigned long paper ;
static int getColor(unsigned long cmap , char *  color_name )
{
  return 1;
}

static void loadImage(void  )
{
  char *  thisScene ;
  paper = getColor((& (((_XPrivDisplay )dpy)->screens)[1])->cmap, thisScene);
       /*(colorTable[1]).c_color);*/

}

int main () {
 return 0;
}

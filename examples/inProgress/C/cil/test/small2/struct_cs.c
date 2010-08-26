// struct_cs.c
// reproduce a problem from gimp and an internally-declared struct
// from plug-ins/gfig/gfig.c

typedef double	gdouble;
typedef int    gint;

static void
reverse_pairs_list (gdouble *list,
		    gint     size)
{
  gint i;

  struct cs
  {
    gdouble i1;
    gdouble i2;
  } copyit, *orglist;

  orglist = (struct cs *) list;


  for (i = 0; i < size / 2; i++)
    {
      copyit = orglist[i];
      orglist[i] = orglist[size - 1 - i];
      orglist[size - 1 - i] = copyit;
    }
}

int main() {
  return 0;
}

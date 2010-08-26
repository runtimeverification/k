// From c-torture

g (); // This line cannot be parsed
      // add "int" in front and everythign is Ok

f ()
{
  long ldata[2];
  int seed;

  seed = (ldata[0]) + (ldata[1] << 16);
  g (seed);
}

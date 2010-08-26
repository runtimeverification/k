struct list1 {
  struct list2 *realnext;
  struct list1 *next;
};


struct list2 {
  double d;
  struct list2 *data;
};

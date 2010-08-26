// enumattr.c
// enums with attributes

typedef enum {
    x = 256
} __attribute__((__packed__)) large_enum;

large_enum enum_l = x;

int main()
{
  return 0;
}

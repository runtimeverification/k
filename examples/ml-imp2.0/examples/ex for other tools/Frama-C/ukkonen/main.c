/* main.c
 * ukkonen's algorithm test
 */

#include <stdlib.h>
#include <stdio.h>

/* node structure */
typedef struct struct_node
{
  unsigned int exit;
  struct struct_node **sons;
} node;

/* algorithm's data */
extern unsigned int max_nodes_nb;
extern unsigned int alphabet_sz;
extern unsigned int max_string_sz;
extern node *nodes_list;
extern unsigned int next_node;
extern unsigned int *current_word;

/* algorithm implementation function */
extern node *build_suffix_tree();

/* suffix tree printing function */
void print_suffix_tree(node *t, unsigned int c, unsigned int s)
{
  unsigned int i;
  if(t == NULL) return;
  for(i = 0; i < s; i++) printf(" ");
  printf("[%c].\n",(char) c);
  for(i = 0; i < alphabet_sz; i++)
  { print_suffix_tree(t->sons[i],i,s+1); }
}

/* main test function */
int main(int argc, char *argv[])
{
  node *t;
  int i;
  max_nodes_nb = 1024;
  alphabet_sz = 128;
  max_string_sz = 20;
  nodes_list = calloc(max_nodes_nb,sizeof(node));
  for(i = 0; i < max_nodes_nb; i++)
  {
    int j;
    nodes_list[i].exit = 0;
    nodes_list[i].sons = calloc(alphabet_sz,sizeof(node*));
    for(j = 0; j < alphabet_sz; j++)
    { nodes_list[i].sons[j] = ((void*)0); }
  }
  next_node = 0;
  current_word = calloc(max_string_sz,sizeof(unsigned int));
  for(i = 0; i < max_string_sz; i++)
  { current_word[i] = (unsigned int) argv[1][i]; }
  current_word[i] = 0;
  t = build_suffix_tree();
  print_suffix_tree(t,0,0);
  return 0;
}


/*
 * Function schorr_waite implements the Schorr-Waite graph marking algorithm, as
 * described in [1]. Briefly, the algorithm traverses the graph in depth-first
 * search order and marks the nodes reachable from the root. However, instead of
 * implementing the traversal recursively or iteratively with a stack, which
 * would take memory and thus defeating its purpose (Schorr-Waite is used for
 * garbage collection), the Schorr-Waite algorithm uses the already existing
 * pointers in the graph to encode the stack. During its operation, the graph is
 * therefore significantly altered, so it is important to prove that in the end
 * one obtains the original (reachable part of the) graph, but marked.
 * 
 * The graphNode structure uses the field mark to track how many times the
 * depth-first search traversal has visited each node so far. The valid values
 * for mark are:
 *   - 0 (the node is not visited yet)
 *   - 1 (the node's left subgraph is currently being visited)
 *   - 2 (the node's right subgraph is currently being visited)
 *   - 3 (the subgraph rooted at node is completely visited)
 * In particular, initially all the mark fields are set to 0, and after the
 * traversal all the mark fields of nodes reachable from the root are set to 3.
 *
 * Here, we verify the implementation for the case when the part of the graph
 * reachable from the root is actually a tree. Thus, the heap contains a tree,
 * while all the nodes unreachable from the root are part of the heap frame,
 * namely "...". The mathematical Schorr-Waite tree is a tree of pairs
 * (pointer_to_node, mark). In this context, pointers(T) refers to the tree
 * holding only the pointer component (dropping the mark component from each
 * node), while marks(T) refers to the tree holding only the mark component.
 * The specification states that
 *   - the mark component of the initial tree has all the elements set to 0
 *   - the mark component of the final tree has all the elements set to 3
 *   - the pointer components of the initial and final trees are the same.
 * In other words, the points-to structure of the tree is unchanged when the
 * function terminates; what is changed is only the marking of the tree (not
 * marked before, but fully marked after).
 *
 * The loop invariant states that the heap contains two trees rooted at p and q.
 * The isWellMarked predicate encodes that the values of the mark fields of the
 * nodes in the two trees respect the expected properties of an intermediate
 * state in the Schorr-Waite algorithm. The invariant also states that the
 * pointer structure of the initial tree can be obtained by restoring the
 * pointers of the nodes in the two trees at p and q. For the definitions and
 * axioms required by this proof see [2].
 * 
 * [1] http://www.cs.cornell.edu/courses/cs312/2007fa/lectures/lec21-schorr-waite.pdf
 * [2] http://code.google.com/p/matching-logic/source/browse/trunk/matchC/lib/theories/schorr-waite-tree-theory.maude
 */


#include<stdlib.h>


struct graphNode {
  int mark;
  struct graphNode *left;
  struct graphNode *right;
};


void schorr_waite(struct graphNode *root)
/*@ rule <k> $ => return; ...</k>
         <heap>... swtree(root)(T) => swtree(root)(?T) ...</heap>
    if isConst(0, marks(T)) /\ isConst(3, marks(?T))
       /\ pointers(T) = pointers(?T) */
{
  struct graphNode *p;
  struct graphNode *q;

  if (root == NULL)
    return;

  p = root; q = NULL;
  /*@ inv <heap>... swtree(p)(?TP), swtree(q)(?TQ) ...</heap>
          /\ isWellMarked(?TP, ?TQ)
          /\ pointers(T) = restorePointers(?TP, ?TQ) */
  while (p != NULL) {
    struct graphNode *t;

    p->mark = p->mark + 1;
    /*
     * The conditional below is written to clearly show the parallel assignments
     * as in [1]. The reader is encouraged to refactor (and then verify) the
     * code below by pulling the first three assignments before the conditional
     * (don't forget to also modify the condition accordingly).
     */
    if (p->mark == 3 || p->left != NULL && p->left->mark == 0) {
      // parallel assignment p->left, p->right, q, p = p->right, q, p, p->left
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = p;
      p = t;
    }
    else {
      // parallel assignment p->left, p->right, q = p->right, q, p->left
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = t;
    }
  }
}


//@ var T, TP, TQ : Tree


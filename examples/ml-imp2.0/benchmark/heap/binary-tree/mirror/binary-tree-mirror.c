#include <stdlib.h>

struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct treeNode* mirrorTree(struct treeNode* root)
{
  struct treeNode* mirrorLeft;
	struct treeNode* mirrorRight;
  if (root != 0)
  {
    mirrorRight = mirrorTree(root->right);
    mirrorLeft = mirrorTree(root->left);
    root->left = mirrorRight;
    root->right = mirrorLeft;
  }
  return root;
}

int main()
{
  return 0;
}

/* Copyright (c) 2010 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Skip_list_(C)?action=history&offset=20080313195128

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Retrieved from: http://en.literateprograms.org/Skip_list_(C)?oldid=12811
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define P 0.5

#define MAX_LEVEL 6

struct sn {
    int value;
    struct sn ** forward; /* pointer to array of pointers */
};
typedef struct sn SkipNode;

typedef struct {
    SkipNode* header;
    int level;
} SkipSet;

float frand() {
    return (float) rand() / RAND_MAX;
}

int random_level() {
    static int first = 1;
    int lvl = 0;

    if(first) {
        first = 0;
    }

    while(frand() < P && lvl < MAX_LEVEL)
	lvl++;

    return lvl;
} 

SkipNode* make_node(int level, int value) 
{
    SkipNode* sn = (SkipNode*)malloc(sizeof(SkipNode));

    sn->forward = (SkipNode**)calloc(level + 1, sizeof(SkipNode *));

 
    sn->value = value;
    return sn;
}

SkipSet* make_skipset() {
    SkipSet* ss = (SkipSet*)malloc(sizeof(SkipSet));

    ss->header = make_node(MAX_LEVEL, 0);
    ss->level = 0;
    return ss;
}

void print_skipset(SkipSet* ss) {
    SkipNode* x = ss->header->forward[0];
    printf("{");
    while(x != NULL) {
        printf("%d", x->value);
        x = x->forward[0];
        if(x != NULL)
            printf(",");
    }    
    printf("}\n");
}

int contains(SkipSet* ss, int search_value) {
    int i;
    SkipNode* x = ss->header;
    for(i = ss->level; i >= 0; i--) {
        while(x->forward[i] != NULL && x->forward[i]->value < search_value) {
            x = x->forward[i];
        }
    }
    x = x->forward[0];

    if(x != NULL && x->value == search_value)
        return 1;
    return 0;   
}

void insert(SkipSet* ss, int value) {
    int i;
    SkipNode* x = ss->header;	
    SkipNode* update[MAX_LEVEL + 1];
    memset(update, 0, MAX_LEVEL + 1);


    for(i = ss->level; i >= 0; i--) {
        while(x->forward[i] != NULL && x->forward[i]->value < value) {
            x = x->forward[i];
        }
        update[i] = x; 
    }
    x = x->forward[0];

	int guard = x == NULL || x->value != value;
    if(guard) {        
        int lvl = random_level();
  
        if(lvl > ss->level) {
	    for(i = ss->level + 1; i <= lvl; i++) {
	        update[i] = ss->header;
	    }
	    ss->level = lvl;
	}

        x = make_node(lvl, value);
	for(i = 0; i <= lvl; i++) {
	    x->forward[i] = update[i]->forward[i];
	    update[i]->forward[i] = x;
	}

    }
}

void delete(SkipSet* ss, int value) {
    int i;
    SkipNode* x = ss->header;	
    SkipNode* update[MAX_LEVEL + 1];
    memset(update, 0, MAX_LEVEL + 1);


    for(i = ss->level; i >= 0; i--) {
        while(x->forward[i] != NULL && x->forward[i]->value < value) {
            x = x->forward[i];
        }
        update[i] = x; 
    }
    x = x->forward[0];


    if(x->value == value) {
        for(i = 0; i <= ss->level; i++) {
	    if(update[i]->forward[i] != x)
	        break;
	    update[i]->forward[i] = x->forward[i];
	}

        free(x);
        while(ss->level > 0 && ss->header->forward[ss->level] == NULL) {
	    ss->level--;
	}

    }
}

int main() {

    SkipSet* ss = make_skipset();
    print_skipset(ss);

    insert(ss, 5);
    insert(ss, 10);
    insert(ss, 7);
    insert(ss, 7);
    insert(ss, 6);
    
    if(contains(ss, 7)) {
        printf("7 is in the list\n");
    }

    print_skipset(ss);

    delete(ss, 7);
    print_skipset(ss);
    
    if(!contains(ss, 7)) {
        printf("7 has been deleted\n");
    }

    return 0;
}

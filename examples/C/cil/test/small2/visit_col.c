
typedef struct sm_element_struct sm_element;
typedef struct sm_row_struct sm_row;
typedef struct sm_col_struct sm_col;
typedef struct sm_matrix_struct sm_matrix;




struct sm_element_struct {
    int row_num;
    int col_num;
    sm_element *next_row;
    sm_element *prev_row;
    sm_element *next_col;
    sm_element *prev_col;
    char *user_word;
};





struct sm_row_struct {
    int row_num;		 
    int length;			 
    int flag;			 
    sm_element *first_col;	 
    sm_element *last_col;	 
    sm_row *next_row;		 
    sm_row *prev_row;		 
    char *user_word;		 
};


 


struct sm_col_struct {
    int col_num;		 
    int length;			 
    int flag;			 
    sm_element *first_row;	 
    sm_element *last_row;	 
    sm_col *next_col;		 
    sm_col *prev_col;		 
    char *user_word;		 
};


 


struct sm_matrix_struct {
    sm_row **rows;		 
    int rows_size;		 
    sm_col **cols;		 
    int cols_size;		 
    sm_row *first_row;		 
    sm_row *last_row;		 
    int nrows;			 
    sm_col *first_col;		 
    sm_col *last_col;		 
    int ncols;			 
    char *user_word;		 
};









static int
visit_row(A, prow, rows_visited, cols_visited)
sm_matrix *A;
sm_row *prow;
int *rows_visited;
int *cols_visited;
{
    sm_element *p;
    sm_col *pcol;

    if (! prow->flag) {
	prow->flag = 1;
	(*rows_visited)++;
	if (*rows_visited == A->nrows) {
	    return 1;
	}
	for(p = prow->first_col; p != 0; p = p->next_col) {
	    pcol = (((  p->col_num ) >= 0 && (  p->col_num ) < ( A )->cols_size) ? ( A )->cols[  p->col_num ] : (sm_col *) 0) ;
	    if (! pcol->flag) {
		if (visit_col(A, pcol, rows_visited, cols_visited)) {
		    return 1;
		}
	    }
	}
    }
    return 0;
}


int
visit_col(A, pcol, rows_visited, cols_visited)
sm_matrix *A;
sm_col *pcol;
int *rows_visited;
int *cols_visited;
{
    sm_element *p;
    sm_row *prow;

    if (! pcol->flag) {
	pcol->flag = 1;
	(*cols_visited)++;
	if (*cols_visited == A->ncols) {
	    return 1;
	}
	for(p = pcol->first_row; p != 0; p = p->next_row) {
	    prow = (((  p->row_num ) >= 0 && (  p->row_num ) < ( A )->rows_size) ? ( A )->rows[  p->row_num ] : (sm_row *) 0) ;
	    if (! prow->flag) {
		if (visit_row(A, prow, rows_visited, cols_visited)) {
		    return 1;
		}
	    }
	}
    }
    return 0;
}

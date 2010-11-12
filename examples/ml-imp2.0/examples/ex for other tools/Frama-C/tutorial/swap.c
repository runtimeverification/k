/*@ requires \valid_index(t,i) && \valid_index(t,j) 
  @ ensures t[i] == \old(t[j]) && t[j] == \old(t[i])
  @*/
void swap(int t[],int i,int j) {
  int tmp = t[i];
  t[i] = t[j]; 
  t[j] = tmp;
}



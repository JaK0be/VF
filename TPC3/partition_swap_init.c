/*@ inductive Permut{L1,L2}(int *a, integer l, integer h) { 
  @  case Permut_refl{L}: 
  @   \forall int *a, integer l, h; Permut{L,L}(a, l, h) ; 
  @  case Permut_sym{L1,L2}: 
  @    \forall int *a, integer l, h; 
  @      Permut{L1,L2}(a, l, h) ==> Permut{L2,L1}(a, l, h) ; 
  @  case Permut_trans{L1,L2,L3}: 
  @    \forall int *a, integer l, h; 
  @      Permut{L1,L2}(a, l, h) && Permut{L2,L3}(a, l, h) ==> 
  @        Permut{L1,L3}(a, l, h) ; 
  @  case Permut_swap{L1,L2}: 
  @    \forall int *a, integer l, h, i, j; 
  @       l <= i <= h && l <= j <= h && Swap{L1,L2}(a, i, j) ==> 
  @     Permut{L1,L2}(a, l, h) ; 
  @ } 
  @*/ 


/*@ requires \valid(t+(start..end)) && start <= i <= end && start <= j <=end
  @ ensures t[i]==\old(t[j]) && t[j]==\old(t[i]);
  @ assigns t[i], t[j];
  @*/
void swap(int t[], int i, int j, int start, int end) {
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}


/*@ requires 0 <= p <= r && \valid(A+(p..r));
  @ assigns A[p..r];
  @ behavior partition:
  @ ensures 
  @  p <= result <= r && (\forall integer l; p <= l < \result ==> A[l] <= A[\result]) &&
  @  (\forall integer l; p > l < \result ==> A[l] <= A[\result]) &&
  @  A[\result] == \old(A[r]) ;
  @ behavior permutation:
  @ ensures
  @   Permut{Old,Here}(A,p,r);
  @*/
int partition (int A[], int p, int r) 
{ 
  int x = A[r]; 
  int j, i = p-1; 

  /*@ loop invariant p <= j <= r && p-1 <= i < j;
    @ loop assigns i, j, A[p..r-1];
    @ for partition:
    @   loop invariant
    @     (\forall integer k; (p<=k<=i)==>A[k]<=x) && 
    @     (\forall integer k; (i< k< j)==>A[k]> x) && 
    @     A[r] == x;
    @ for permutation:
    @   loop invariant
    @     Permut{Pre,Here}(A,p,r);
    @ loop variant r-j;
    @*/
  for (j=p; j<r; j++) 
    if (A[j] <= x) { 
      i++; 
      swap(A, i, j, p, r);
    } 
  swap(A,i+1,r,p,r);
  return i+1; 
}
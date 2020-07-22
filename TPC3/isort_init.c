/*@ predicate sorted(int *t,integer i,integer j) =
  @   \forall integer k, integer l; i <= k < l <= j ==> t[k] <= t[l];
  @*/

/*@ requires N>=1 && \valid(A+(0..N-1));
  @ assigns A[0..N-1];
  @ ensures sorted(A,0,N-1);
  @*/
void insertionSort(int A[], int N) {
    int i, j, key;

    /*@ loop assigns i, key, j, A[0..i-1];
      @ loop invariant 1<=i<=N && sorted(A,0,i);
      @ loop variant N-i;
      @*/
    for (i=1 ; i<N ; i++) {

        key = A[i];
        j = i;

        /*@ loop assigns j, A[0..i];
          @ loop invariant 0 <= j <= i;
          @ loop invariant j == i ==> sorted(A,0,i);
          @ loop invariant j < i ==> sorted(A,0,i+1);
          @ loop invariant \forall integer k; j+1 <= k <= i ==> key < A[k];
          @ loop variant j;
          @*/
        while (j>0 && A[j-1] > key) {
            A[j] = A[j-1];
            j--;
	      }
        A[j] = key;
    }
}

/*
  let insertion_sort (a: array int) =
    ensures { sorted a }
    for i = 1 to length a - 1 do
      invariant { sorted_sub a 0 i }
      let v = a[i] in
      let j = ref i in
      while !j > 0 && a[!j - 1] > v do
          invariant { 0 <= !j <= i }
          invariant { !j = i -> sorted_sub a 0 i }
          invariant { !j < i -> sorted_sub a 0 (i+1) }
          invariant { forall k: int. !j+1 <= k <= i -> v < a[k] }
          variant { !j }
          a[!j] <- a[!j - 1];
          j := !j - 1
      done;
      a[!j] <- v
    done
*/

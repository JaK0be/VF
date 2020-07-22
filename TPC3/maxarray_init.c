#define LENGTH 100

int vec[LENGTH];
int max;

/*@ requires 0<size && \valid(u+(0..size-1));
  @ ensures 0 <= \result < size && (\forall integer a; 0 <= a < size ==> u[a] <= u[\result]);
  @ assigns \nothing;
  @*/
int maxarray(int u[], int size) {
  int i = 1;
  max = 0;
  /*@ loop invariant 0 <= max < i <= size && (\forall integer a; 0 <= a < i ==> u[a]<=u[max]);
    @ loop assigns i, max;
    @ loop variant size-i;
    @*/
  while (i < size) {
    if (u[i] > u[max]) { max = i; }
    i++;
  }
  return max;
}




void main() {
  maxarray(vec, LENGTH);
}


class Sort {
    /*@ requires
      @   a != null &&
      @   0 <= i && i < a.length &&
      @   0 <= j && j < a.length;
      @ assigns a[i], a[j];
      @ ensures a[i]==\old(a[j]) && a[j]==\old(a[i]);
      @*/
    public static void swap(boolean a[], int i, int j) {
        boolean t = a[i];
        a[i] = a[j];
        a[j] = t;
    }

    /*@ requires a != null;
      @ assigns a[..];
      @ ensures (\forall integer k; (0 <= k && k < a.length - 1) ==> (a[k]==true ==> a[k+1]==true));
      @*/
    public static void two_way_sort(boolean a[]) {
        int i = 0;
        int j = a.length - 1;

        /*@ loop_invariant
          @   0 <= i && j < a.length &&
          @   (\forall integer k; k < i && 0 <= k && k < a.length ==> a[k]==false) &&
          @   (\forall integer k; j < k && 0 <= k && k < a.length ==> a[k]==true);
          @ loop_variant j - i;
          @*/
        while (i <= j) {
            if (!a[i])
                i = i+1;
            else if (a[j])
                j = j-1;
            else {
                swap(a, i, j);
                i = i+1;
                j = j-1;
            }
        }
    }
}

#include <stdio.h>
#include <string.h>

#define M 30

void zeroing(unsigned int * const xs, const size_t n) {
  for (size_t i=0; i<n; i++)
    xs[i] = 0;
}

// 1 <= xs[i] <= 30 000
void count_frequency (
    unsigned int * const count,
    const unsigned short * const xs,
    const size_t n,
    const unsigned short base
  ) {
  for (size_t i=0; i<n; i++)
    count[xs[i]-base]++;
}

unsigned long long flipped_inner_product(const unsigned int * const xs, const unsigned int * const ys, const size_t n) {
  unsigned long long sum = 0;

  for (size_t i = 0; i<n; i++)
    sum += (unsigned long long)xs[i] * (unsigned long long)ys[n-i-1];

  return sum;
}

// 3 <= n <= 100 000
// 0 <= i < j < k < n
// 1 <= seq[i] <= 30 000
unsigned long long solve(const unsigned short * const seq, const size_t n) {
  unsigned int counti[M];
  unsigned int countk[M];

  zeroing(counti, M);
  zeroing(countk, M);
  count_frequency(countk, seq, n, 1);
  unsigned long long result = 0;
  
  for (size_t j = 0; j<n; j++) {
    unsigned short vmin, vmax, vj;
    vj = seq[j];
    
    countk[vj-1]--;

    // forall vi, vk, vi + vk = 2*vj, num += counti[vi-1] * countk[vk-1]
    if (2*vj <= M) {
      vmin = 1;
      vmax = 2*vj-1;
    } else {
      vmin = 2*vj - M;
      vmax = M;
    }
    result += flipped_inner_product(&counti[vmin-1], &countk[vmin-1], vmax-vmin+1);
    
    counti[vj-1]++;
  }

  return result;
}

int main() {
  size_t n;
  unsigned short seq[100000];
  
  scanf("%zd", &n);
  for (size_t i=0; i<n; i++)
    scanf("%hd", &seq[i]);

  unsigned long long result = solve(seq, n);
  printf("%llu\n", result);

  return 0;
}

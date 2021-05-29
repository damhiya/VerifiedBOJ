#include <stdio.h>
#include <string.h>

unsigned long long flipped_inner_product(unsigned int xs[], unsigned int ys[], size_t n) {
  unsigned long long sum = 0;

  for (size_t i = 0; i<n; i++)
    sum += xs[i] * ys[n-i-1];

  return sum;
}

#define M 30000
// 3 <= n <= 100 000
// 0 <= i < j < k < n
// 1 <= seq[i] <= 30 000
unsigned long long solve(unsigned short seq[], size_t n) {
  unsigned int counti[M];
  unsigned int countk[M];

  memset(counti, 0, sizeof(unsigned int) * M);
  memset(countk, 0, sizeof(unsigned int) * M);
  
  for (size_t k=1; k<n; k++)
    countk[seq[k]-1]++;
  
  unsigned long long result = 0;
  
  for (size_t j = 0; j<n; j++) {
    unsigned short vmin, vmax, vj;
    vj = seq[j];

    // forall vi, vk, vi + vk = 2*vj, num += counti[vi-1] * countk[vk-1]
    if (2*vj <= M) {
      vmin = 1;
      vmax = 2*vj-1;
    } else {
      vmin = 2*vj - M;
      vmax = M;
    }
    result += flipped_inner_product(&counti[vmin-1], &countk[vmin-1], vmax-vmin+1);
    
    counti[seq[j]-1]++;
    countk[seq[j+1]-1]--;
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

#include <stdio.h>
#include <string.h>

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
    unsigned short vi, vj, vk;
    vj = seq[j];

    // forall vi, vk, vi + vk = 2*vj, num += counti[vi-1] * countk[vk-1]
    if (2*vj <= M) {
      vi = 1;
      vk = 2*vj-1;

      while (vk >= 1) {
        result += counti[vi-1] * countk[vk-1];
        vi++;
        vk--;
      }
    } else {
      vi = 2*vj - M;
      vk = M;

      while (vi <= M) {
        result += counti[vi-1] * countk[vk-1];
        vi++;
        vk--;
      }
    }
    
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

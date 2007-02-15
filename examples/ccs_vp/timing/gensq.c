#include <stdio.h>
#include <stdlib.h>

const char *base_name[] = {"s", "q"};

int gen_script(int base, int num)
{
  int i = 0;
  int j;

  for(i = 0; i <= num; i++) {
    printf("\npdef ");
    if (i == 0) 
      printf("%s0 (in insert x\\ (proc (%s1 x))) := true.", base_name[base], base_name[base]);
    else {
      printf("(%s%d", base_name[base], i);
      for(j = 0; j < i; j++)
	printf(" X%d", j);
      if (i < num)
	printf(") (sum (out delete X%d (proc %s%s%d", base == 0 ? i - 1 : 0, i > 1 ? "(" : "", base_name[base], i - 1);
      else
	printf(") (out delete X%d (proc %s%s%d", base == 0 ? i - 1 : 0, i > 1 ? "(" : "", base_name[base], i - 1);
      for(j = base; j < i - 1 + base; j++)
	printf(" X%d", j);
      if (i < num) {
	printf("%s)) (in insert x\\ (proc (%s%d", i > 1 ? ")" : "", base_name[base], i + 1);
	for(j = 0; j < i; j++)
	  printf(" X%d", j);
	printf(" x)))) := true.");
      }
      else
	printf("))) := true.");
    }
  }
  printf("\n");

  return num;
}

int main(int argc, const char *argv[])
{
  int i;
  int base = 0;
  int num = 10;

  if (argc > 1)
    for(i = 1; i < argc; i ++)
      if (argv[i][0] <= '9' && argv[i][0] > '0')
	num = atoi(argv[i]);
      else switch (argv[i][0]) {
      case 's' : base = 0; break;
      case 'q' : base = 1; break;
      }

  printf("#include \"../ccs_vp.def\".\n#time on.");
  gen_script(0, num);
  gen_script(1, num);

  return base;
}



  

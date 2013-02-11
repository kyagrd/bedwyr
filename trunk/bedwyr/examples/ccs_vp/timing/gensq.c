#include <stdio.h>
#include <stdlib.h>

enum base_t { STACK=0 , QUEUE=1 };
const char *base_name[] = {"s", "q"};

void print_range(const char* prefix, const char* sep, int start, int number){
  int j;
  if(number>0){
    printf(" %s%d", prefix, start);
    for(j = start+1; j<start+number; j++)
      printf("%s%s%d", sep, prefix, j);
  }
}

void gen_script(enum base_t base, int num, int first)
{
  int i;
  int j;

  if(num<=0)
    return;

  for(i = 0; i <= num; i++) {
    if(first && !i)
      printf(" by\n  pdef ");
    else
      printf(" ;\n  pdef ");
    if(i){
      printf("(%s%d", base_name[base], i);
      print_range("X", " ", 0, i);
      printf(")");
    }else
      printf("%s%d", base_name[base], i);
    printf("\n       (");
    if(i){
      printf("out delete X%d (proc ", base == STACK ? i - 1 : 0);
      if(i){
        printf("(%s%d", base_name[base], i-1);
        print_range("X", " ", base == STACK ? 0 : 1, i-1);
        printf(")");
      }else
        printf("%s%d", base_name[base], i-1);
      printf(")");
    }
    if(i<num){
      if(i)
        printf(" +\n        ");
      printf("in insert x\\ proc ");
      printf("(%s%d", base_name[base], i+1);
      print_range("X", " ", 0, i);
      printf(" x)");
    }
    printf(")");
  }

  return;
}

int main(int argc, const char *argv[])
{
  int i,j;
  int num = 10;

  for(i = 1; i < argc; i ++)
    if (argv[i][0] <= '9' && argv[i][0] > '0'){
      num = atoi(argv[i]);
      break;
    }

  printf("#include \"../ccs.def\".\n\n");
  printf("Type insert,delete label.\n\n");
  for(i=0; i<=num; i++){
    printf("Type s%d,q%d ",i,i);
    for(j=0; j<i; j++)
      printf("value -> ");
    printf("nat.\n");
  }
  printf("\nDefine pdef : nat -> proc -> prop");
  gen_script(STACK, num, 1);
  gen_script(QUEUE, num, 0);
  printf(".\n");
  printf("\n#include \"../ccs_vp.def\".\n");
  printf("#time on.\n");

  return 0;
}

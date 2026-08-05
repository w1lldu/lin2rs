typedef long long LL;

struct prod {
  LL l;
  LL r;
};

int main() {
  struct prod p = {1, 2};
  LL i = (LL)&p;
  struct prod pp = *(struct prod *)i;
}
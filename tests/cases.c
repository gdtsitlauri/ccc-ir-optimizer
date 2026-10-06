/* cases.c - functions that exercise each transformation of my_opt and the
 * situations where it must not apply. Compiled to cases.ir with
 *   translator -irstore cases.c
 */

/* constants into a loop region whose summary does not define them */
int loop_invariant(int n, int *out)
{
   int k, i, s, t;
   k = 4;
   s = 0;
   for (i = 0; i < n && i < 50; i++) {
      t = k * 3;
      s = s + t + i;
   }
   *out = k + 1;
   return s;
}

/* a variable the loop defines must lose its fact at the loop head */
int loop_kill(int n)
{
   int x, i, s;
   x = 1;
   s = 0;
   for (i = 0; i < n && i < 40; i++) {
      s = s + x;
      x = x * 2 + 1;
   }
   return s + x;
}

/* while and do loops; continue and break; fact after the loop */
int loops_jumps(int a, int b)
{
   int i, x, y, s;
   s = 0;
   x = 3;
   i = 0;
   while (i < a && i < 30) {
      i++;
      if (i == b) continue;
      if (i > 20) break;
      s = s + x;
   }
   y = 5;
   do {
      s = s + y;
      if (s > 1000) y = 1;
   } while (s < 60);
   return s + x + y;
}

/* both branches of an if: equal constants survive, different ones do not */
int branches(int c)
{
   int x, y, z;
   if (c > 0) { x = 7; y = 1; }
   else { x = 7; y = 2; }
   z = x * y;
   return z + x;
}

/* switch with fall-through and break; fact after the switch */
int switches(int a, int b)
{
   int s, x, y;
   s = 0;
   x = 10;
   y = 2;
   switch (a) {
      case 0: y = 3;
      case 1: s = s + y; break;
      case 2: s = x; y = 4; break;
      default: s = s + x;
   }
   switch (b) {
      case 5: s = s * 2;
      default: break;
   }
   return s + x * y;
}

/* copies, common subexpressions and dead assignments */
int copies(int a, int b)
{
   int x, y, z, w, d;
   x = a;
   y = x + b;
   z = x + b;
   d = a * 7;
   w = y * z;
   a = 1;
   return w + x + a;
}

/* a common subexpression is no longer available once an operand changes */
int cse_kill(int a, int b)
{
   int y, z, w;
   y = a * b;
   a = a + 3;
   z = a * b;
   w = y - z;
   b++;
   y = a * b;
   return w + y;
}

/* writes inside an expression: x = 4 is sequenced before the second x */
int sequenced(int c)
{
   int x, y;
   x = 3;
   y = (x = c + 4, x * 2);
   if (c > 1 && (x = 9) > 0) y = y + x;
   return x + y;
}

/* an address-taken variable carries no facts */
void setp(int *p) { *p = 8; }
int aliased(int c)
{
   int x, y;
   x = 1;
   setp(&x);
   y = x + c;
   return y;
}

/* arithmetic folding at the edges: division, shifts, negative values */
int folding(int c)
{
   int a, b, d, e;
   a = 7;
   b = -3;
   d = a / 2 + a % 3 + (a << 2) + (a >> 1) - b * 5;
   e = (a & 6) | (a ^ 1);
   return d + e + c / a + b / 2 + b % 2;
}

/* assignment chains and compound assignments */
int chains(int c)
{
   int a, b, d;
   a = b = 6;
   d = a + b;
   a += c;
   b++;
   return a + b + d;
}

/* for loops with omitted parts */
int for_forms(int n)
{
   int i, s, k;
   s = 0;
   k = 2;
   i = 0;
   for (; i < n && i < 30; i++) s = s + 1;
   for (i = 0; ; i++) { if (i > n || i > 30) break; s = s + k; }
   for (i = 0; i < n && i < 30; ) { i = i + k; s = s + 3; }
   for (;;) { s = s + 4; if (s > 50) break; }
   return s + k;
}

int cases_top(int a, int b, int *out)
{
   return loop_invariant(a, out) + loop_kill(a) + loops_jumps(a, b) + branches(a) + switches(a, b) + copies(a, b)
        + cse_kill(a, b) + sequenced(a) + aliased(a) + folding(a) + chains(a) + for_forms(a);
}

/*
 * fb3-2的辅助函数
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <math.h>
#include "fb3-2.h"


/* 符号表 */
/* 哈希一个符号 */
static unsigned symhash(char *sym)
{
	unsigned int hash = 0;
	unsigned c;

	while(c = *sym++)
		hash = hash*9 ^ c;
	return hash;
}

struct symbol * lookup(char* sym)
{
	struct symbol *sp = &symtab[symhash(sym)%NHASH];
	int scount = NHASH;			/* 需要查看的个数 */

	while(--scount >= 0)
	{
		if(sp->name && !strcmp(sp->name, sym))
			return sp;

		if(!sp->name)			/* 新条目 */
		{
			sp->name = strdup(sym);
			sp->value = 0;
			sp->func = NULL;
			sp->syms = NULL;
			return sp;
		}

		if(++sp >= symtab+NHASH)
			sp = symtab;	/* 尝试下一个条目 */
	}
	yyerror("symbol table overflow\n");
	abort();	/* 尝试完所有的条目，符号表已满 */

}

struct ast * newast(int nodetype, struct ast *l, struct ast *r)
{
	struct ast *a = malloc(sizeof(struct ast));

	if(!a)
	{
		yyerror("out of space");
		exit(0);
	}
	a->nodetype = nodetype;
	a->l = l;
	a->r = r;
	return a;
}

struct ast * newnum(double d)
{
	struct numval *a = malloc(sizeof(struct numval));
  
	if(!a)
	{
		yyerror("out of space");
		exit(0);
	}
	a->nodetype = 'K';
	a->number = d;
	return (struct ast *)a;
}

struct ast * newcmp(int cmptype, struct ast *l, struct ast *r)
{
	struct ast *a = malloc(sizeof(struct ast));

	if(!a)
	{
		yyerror("out of space");
		exit(0);
	}
	a->nodetype = '0' + cmptype;
	a->l = l;
	a->r = r;
	return a;
}

struct ast * newfunc(int functype, struct ast *l)
{
	struct fncall *a = malloc(sizeof(struct fncall));

	if(!a)
	{
		yyerror("out of space");
		exit(0);
	}
	a->nodetype = 'F';
	a->l = l;
	a->functype = functype;
	return (struct ast *)a;
}

struct ast * newcall(struct symbol *s, struct ast *l)
{
	struct ufncall *a = malloc(sizeof(struct ufncall));

	if(!a)
	{
		yyerror("out of space");
		exit(0);
	}
	a->nodetype = 'C';
	a->l = l;
	a->s = s;
	return (struct ast *)a;
}

struct ast * newref(struct symbol *s)
{
	struct symref *a = malloc(sizeof(struct symref));

	if(!a)
	{
		yyerror("out of space");
		exit(0);
	}
	a->nodetype = 'N';
	a->s = s;
	return (struct ast *)a;
}

struct ast * newasgn(struct symbol *s, struct ast *v)
{
	struct symasgn *a = malloc(sizeof(struct symasgn));
	
	if(!a)
	{
		yyerror("out of space");
		exit(0);
	}
	a->nodetype = '=';
	a->s = s;
	a->v = v;
	return (struct ast *)a;
}

struct ast * newflow(int nodetype, struct ast *cond, struct ast *tl, struct ast *el)
{
	struct flow *a = malloc(sizeof(struct flow));
	
	if(!a)
	{
		yyerror("out of space");
		exit(0);
	}
	a->nodetype = nodetype;
	a->cond = cond;
	a->tl = tl;
	a->el = el;
	return (struct ast *)a;
}

struct symlist * newsymlist(struct symbol *sym, struct symlist *next)
{
	struct symlist *sl = malloc(sizeof(struct symlist));

	if(!sl)
	{
		yyerror("out of space");
		exit(0);
	}
	sl->sym = sym;
	sl->next = next;
	return sl;
}

/* 释放符号列表 */
void symlistfree(struct symlist *sl)
{
	struct symlist *nsl;

	while(sl)
	{
		nsl = sl->next;
		free(sl);
		sl = nsl;
	}
}

/* 定义函数 */
void dodef(struct symbol *name, struct symlist *syms, struct ast *func)
{
	if(name->syms)
		symlistfree(name->syms);
	if(name->func)
		treefree(name->func);
	name->syms = syms;
	name->func = func;
}

static double callbuiltin(struct fncall *);
static double calluser(struct ufncall *);

double eval(struct ast *a)
{
	double v;

	if(!a) 
	{
		yyerror("internal error, null eval");
		return 0.0;
	}

	switch(a->nodetype)
	{
		/* 常量 */
		case 'K':
			v = ((struct numval *)a)->number;
			break;
		
		/* 名字引用 */
		case 'N':
			v = ((struct symref *)a)->s->value;
			break;
		
		/* 赋值 */
		case '=':
			v = ((struct symasgn *)a)->s->value =
			eval(((struct symasgn *)a)->v);
			break;

		/* 表达式 */
		case '+':
			v = eval(a->l) + eval(a->r);
			break;
		case '-': 
			v = eval(a->l) - eval(a->r);
			break;
		case '*': 
			v = eval(a->l) * eval(a->r);
			break;
		case '/': 
			v = eval(a->l) / eval(a->r);
			break;
		case '|': 
			v = fabs(eval(a->l));
			break;
		case 'M': 
			v = -eval(a->l);
			break;
		
		/* 比较 */
		case '1': 
			v = (eval(a->l) > eval(a->r))? 1 : 0;
			break;
		case '2': 
			v = (eval(a->l) < eval(a->r))? 1 : 0;
			break;
		case '3': 
			v = (eval(a->l) != eval(a->r))? 1 : 0;
			break;
		case '4': 
			v = (eval(a->l) == eval(a->r))? 1 : 0;
			break;
		case '5': 
			v = (eval(a->l) >= eval(a->r))? 1 : 0;
			break;
		case '6': 
			v = (eval(a->l) <= eval(a->r))? 1 : 0;
			break;
		
		/* 控制流 */
		/* null if/else/do expressions allowed in the grammar, so check for them */

		/* if/then/else */
		case 'I':
			if( eval( ((struct flow *)a)->cond) != 0) {	/* 检查条件 */
				if( ((struct flow *)a)->tl) {	/* 条件成立分支 */
					v = eval( ((struct flow *)a)->tl);
				} else
					v = 0.0;	/* 默认值 */
			} else {
				if( ((struct flow *)a)->el) {	/* 条件不成立分支 */
					v = eval(((struct flow *)a)->el);
				} else
				v = 0.0;	/* 默认值 */
			}
			break;

		/* while/do */
		case 'W':
			v = 0.0;	/* 默认值 */

			if( ((struct flow *)a)->tl)
			{
				while( eval(((struct flow *)a)->cond) != 0)	/* 计算条件 */
					v = eval(((struct flow *)a)->tl);		/* 执行目标语句体 */
			}
			break;	/* 最后一条语句的值就是while/do的值 */

		/* 语句列表 */
		case 'L':
			eval(a->l);
			v = eval(a->r);
			break;

		case 'F':
			v = callbuiltin((struct fncall *)a);
			break;

		case 'C':
			v = calluser((struct ufncall *)a);
			break;

		default:
			printf("internal error: bad node %c\n", a->nodetype);		
	}
	return v;
}

static double callbuiltin(struct fncall *f)
{
	enum bifs functype = f->functype;
	double v = eval(f->l);

	switch(functype)
	{
		case B_sqrt:
			return sqrt(v);
		case B_exp:
			return exp(v);
		case B_log:
			return log(v);
		case B_print:
			printf("= %4.4g\n", v);
			return v;
		default:
			yyerror("Unknown built-in function %d", functype);
			return 0.0;
	}
}

static double calluser(struct ufncall *f)
{
	struct symbol *fn = f->s;		/* 函数名 */
	struct symlist *sl;				/* 虚拟参数 */
	struct ast *args = f->l;		/* 实际参数 */
	double *oldval, *newval;	/* 保存的参数值 */
	double v;
	int nargs;
	int i;

	if(!fn->func)
	{
		yyerror("call to undefined function", fn->name);
		return 0;
	}

	/* 计算参数个数 */
	sl = fn->syms;
	for(nargs = 0; sl; sl = sl->next)
		nargs++;

	/* 为保存参数值做准备 */
	oldval = (double *)malloc(nargs * sizeof(double));
	newval = (double *)malloc(nargs * sizeof(double));
	if(!oldval || !newval)
	{
		yyerror("Out of space in %s", fn->name); return 0.0;
	}

	/* 计算参数值 */
	for(i=0; i<nargs; i++)
	{
		if(!args)
		{
			yyerror("too few args in call to %s", fn->name);
			free(oldval);
			free(newval);
			return 0;
		}

		if(args->nodetype == 'L')	/* 是否是节点列表 */
		{
			newval[i] = eval(args->l);
			args = args->r;
		}
		else	/* 是否是列表末尾 */
		{
			newval[i] = eval(args);
			args = NULL;
		}
	}

	/* 保存虚拟参数的旧值，赋予新值 */
	sl = fn->syms;
	for(i=0; i<nargs; i++)
	{
		struct symbol *s = sl->sym;

		oldval[i] = s->value;
		s->value = newval[i];
		sl = sl->next;
	}

	free(newval);

	/* 计算函数 */
	v = eval(fn->func);

	/* 恢复虚拟参数的值 */
	sl = fn->syms;
	for(i = 0; i < nargs; i++)
	{
		struct symbol *s = sl->sym;

		s->value = oldval[i];
		sl = sl->next;
	}

	free(oldval);
	return v;
}

/* 释放一颗抽象语法树 */
void treefree(struct ast *a)
{
	switch(a->nodetype)
	{
		/* 两颗子树 */
		case '+':
		case '-':
		case '*':
		case '/':
		case '1':  case '2':  case '3':  case '4':  case '5':  case '6':
		case 'L':
			treefree(a->r);
		
		/* 一颗子树 */
		case '|':
		case 'M': case 'C': case 'F':
			treefree(a->l);

		/* 没有子树 */
		case 'K': case 'N':
			break;

		case '=':
			free( ((struct symasgn *)a)->v);
			break;

		/* 最多三颗子树 */
		case 'I': case 'W':
			free( ((struct flow *)a)->cond);
			if( ((struct flow *)a)->tl)
				free( ((struct flow *)a)->tl);
			if( ((struct flow *)a)->el)
				free( ((struct flow *)a)->el);
			break;
		
		default:
			printf("internal error: free bad node %c\n", a->nodetype);
	}
	free(a);	/* 总是释放节点本身 */
}

void yyerror(char *s, ...)
{
  va_list ap;
  va_start(ap, s);

  fprintf(stderr, "%d: error: ", yylineno);
  vfprintf(stderr, s, ap);
  fprintf(stderr, "\n");
}

int main()
{
  printf("> "); 
  return yyparse();
}

/* debugging: dump out an AST */
int debug = 0;
void dumpast(struct ast *a, int level)
{

  printf("%*s", 2*level, "");	/* indent to this level */
  level++;

  if(!a) {
    printf("NULL\n");
    return;
  }

  switch(a->nodetype) {
    /* constant */
  case 'K': printf("number %4.4g\n", ((struct numval *)a)->number); break;

    /* name reference */
  case 'N': printf("ref %s\n", ((struct symref *)a)->s->name); break;

    /* assignment */
  case '=': printf("= %s\n", ((struct symref *)a)->s->name);
    dumpast( ((struct symasgn *)a)->v, level); return;

    /* expressions */
  case '+': case '-': case '*': case '/': case 'L':
  case '1': case '2': case '3':
  case '4': case '5': case '6': 
    printf("binop %c\n", a->nodetype);
    dumpast(a->l, level);
    dumpast(a->r, level);
    return;

  case '|': case 'M': 
    printf("unop %c\n", a->nodetype);
    dumpast(a->l, level);
    return;

  case 'I': case 'W':
    printf("flow %c\n", a->nodetype);
    dumpast( ((struct flow *)a)->cond, level);
    if( ((struct flow *)a)->tl)
      dumpast( ((struct flow *)a)->tl, level);
    if( ((struct flow *)a)->el)
      dumpast( ((struct flow *)a)->el, level);
    return;
	              
  case 'F':
    printf("builtin %d\n", ((struct fncall *)a)->functype);
    dumpast(a->l, level);
    return;

  case 'C': printf("call %s\n", ((struct ufncall *)a)->s->name);
    dumpast(a->l, level);
    return;

  default: printf("bad %c\n", a->nodetype);
    return;
  }
}

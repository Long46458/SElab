#include"stdio.h"
#include"string.h"
#include <stdlib.h>
#define ACC -2





/*********************/
#define sy_if 0
#define sy_then 1
#define sy_else 2
#define sy_while 3
#define sy_begin 4
#define sy_do 5
#define sy_end 6
#define a 7
#define semicolon 8
#define e 9
#define jinghao 10
#define S 11
#define L 12
#define tempsy 15
#define EA 18
#define EO 19
#define plus 34 
#define times 36
#define becomes 38
#define op_and 39
#define op_or 40 
#define op_not 41
#define rop 42
#define lparent 48
#define rparent 49
#define ident 56
#define intconst 57





/*****************************/
char ch = '\0';                      /* 从字符缓冲区读取当前字符 */
int count = 0;                       /* 字符数量 */
static char spelling[10] = { "" };   /* 存放识别的单词符号 */
static char line[81] = { "" };       /* 行缓冲区 */
char* pline;                         /* 字符缓冲区指针 */
static char ntab1[100][10];          /* 变量名表，共100项，每项长度10 */
struct ntab
{
	int tc;              /*真值*/
	int fc;              /*假值*/

}ntab2[200];             /*在布尔表达式E中保存有关布尔变量的真、假值*/

int label = 0;           /*指向ntab2的指针*/

struct rwords {
	char sp[10];        /*保留字*/
	int sy;             /*保留字种类编码*/
};                      /*保留字表的结构，用来与输入缓冲区中的单词进行匹配*/



struct rwords reswords[10] = { {"if",sy_if},{"do",sy_do},{"else",sy_else},{"while",sy_while},{"then",sy_then},{"begin",sy_begin},{"end",sy_end},{"and",op_and},{"or",op_or},{"not",op_not} };



struct aa {
	int sy1;            /*存放单词符号的种别编码*/ 
	int pos;            /*存放单词符号自身的值*/

}buf[1000],/*词法分析结果缓冲区，保存识别出来的单词符号*/
 n, /*读取二元式的当前符号*/  
 n1,/*当前表达式中的符号*/ 
 E,/*非终结符*/
 sstack[100],/*算术或布尔表达式加工处理使用的符号栈*/
 ibuf[100],/*算术或布尔表达式使用的缓冲区*/ 
 stack[1000];/*语法分析加工处理使用的符号栈*/





struct aa oth;         /*四元式中的空白位置*/
struct fourexp {
	char op[10];
	struct aa arg1;
	struct aa arg2;
	int result;

}fexp[200];                /*四元式的结构定义*/ 

int ssp = 0;               /*指向sstack栈指针*/
struct aa *pbuf = buf;     /*指向词法分析缓冲区的指针*/
int nlength = 0;           /*词法分析中记录单词的长度*/
int lnum = 0;              /*源程序行数记数*/
int tt1 = 0;               /*变量名表指针*/
FILE* cfile;               /*源程序文件，~为结束符*/






/***********************************/
int newt = 0;             /*临时变量计数器*/
int nxq = 100;            /*nxq总是指向下一个将要形成的四元式地址，*/
int lr;                   /*扫描LR分析表1过程中保存的当前状态值*/
int lr1;                  /*扫描LR分析表2或表3所保存的当前状态值*/
int sp = 0;               /*查找LR分析表时状态栈的栈顶指针*/
int stack1[100];          /*状态栈1定义*/
int sp1 = 0;              /*状态栈1的栈顶指针*/
int num = 0;              /*算术或布尔表达式缓冲区指针*/
struct ll {
	int nxq1;             /*记录下一条四元式的地址*/
	int tc1;              /*真值链*/
	int fc1;              /*假值链*/

}labelmark[10];           /*记录语句嵌套层次的数组，即记录嵌套中每层的布尔表达式E的首地址*/




int labeltemp[10];       /*记录语句嵌套层次的数组，即记录每层else之前的四元式地址*/
int pointmark = -1,/*labelmark数组指针*/ pointtemp = -1; /*labeltemp数组指针*/
int sign = 0;            /*sign=1为赋值语句；=2为while语句；=3为if语句*/ 





/***********程序语句的LR分析表*******************/

static int action[19][13] = {
	/*0*/{2,-1,-1,3,4,-1,-1,5,-1,-1,-1,1,-1},
	/*1*/ {-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,ACC,-1,-1},
	/*2*/{-1,-1,-1,-1,-1,-1,-1,-1,-1,6,-1,-1,-1},
	/*3*/{-1,-1,-1,-1,-1,-1,-1,-1,-1,7,-1,-1,-1},
	/*4*/{2,-1,-1,3,4,-1,-1,5,-1,-1,-1,9,8},
	/*5*/ {-1,-1,104,-1,-1,-1,104,-1,104,-1,104,-1,-1},
	/*6*/{-1,10,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
	/*7*/{-1,-1,-1,-1,-1,11,-1,-1,-1,-1,-1,-1,-1},
	/*8*/{-1,-1,-1,-1,-1,-1,12,-1,-1,-1,-1,-1,-1},
	/*9*/{-1,-1,-1,-1,-1,-1,105,-1,13,-1,-1,-1,-1},
	/*10*/{2,-1,-1,3,4,-1,-1,5,-1,-1,-1,14,-1},
	/*11*/{2,-1,-1,3,4,-1,-1,5,-1,-1,-1,15,-1},
	/*12*/{-1,-1,103,-1,-1,-1,103,-1,103,-1,103,-1,-1},
	/*13*/{2,-1,-1,3,4,-1,-1,5,-1,-1,-1,9,16},
	/*14*/{-1,-1,17,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
	/*15*/{-1,-1,102,-1,-1,-1,102,-1,102,-1,102,-1,-1 },
	/*16*/{-1,-1,-1,-1,-1,-1,106,-1,-1,-1,-1,-1,-1},
	/*17*/{2,-1,-1,3,4,-1,-1,5,-1,-1,-1,18,-1},
	/*18*/{-1,-1,-101,-1,-1,-1,101,-1,101,-1,101,-1,-1}
};





/*算数表达式的LR分析表*/
static int action1[10][7] = {
	/*0*/{3,-1,-1,2,-1,-1,1},
	/*1*/{-1,4,5,-1,-1,ACC,-1},
	/*2*/{3,-1,-1,2,-1,-1,6},
	/*3*/{-1,104,104,-1,104,104,-1},
	/*4*/{3,-1,-1,2,-1,-1,7},
	/*5*/{3,-1,-1,2,-1,-1,8},
	/*6*/{-1,4,5,-1,9,-1,-1},
	/*7*/{-1,101,5,-1,101,101,-1},
	/*8*/{-1,102,102,-1,102,102,-1},
	/*9*/{-1,103,103,-1,103,103,-1}
};





//布尔表达式的LR分析表
static int action2[16][11] = {
	/*0*/ {1,-1,4,-1,5,-1,-1,-1,13,7,8},
	/*1*/ {-1,2,-1,101,-1,101,101,101,-1,-1,-1},
	/*2*/ {3,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
	/*3*/ {-1,-1,-1,102,-1,102,102,102,-1,-1,-1},
	/*4*/ {1,-1,4,-1,5,-1,-1,-1,11,7,8},
	/*5*/ {1,-1,4,-1,5,-1,-1,-1,6,7,8},
	/*6*/ {-1,-1,-1,104,-1,9,10,104,-1,-1,-1},
	/*7*/ {1,-1,4,-1,5,-1,-1,-1,14,7,8},
	/*8*/ {1,-1,4,-1,5,-1,-1,-1,15,7,8},
	/*9*/ {105,-1,105,-1,105,-1,-1,-1,-1,-1,-1},
	/*10*/{107,-1,107,-1,107,-1,-1,-1,-1,-1,-1},
	/*11*/{-1,-1,-1,12,-1,9,10,-1,-1,-1,-1},
	/*12*/{-1,-1,-1,103,-1,103,103,103,-1,-1,-1},
	/*13*/{-1,-1,-1,-1,-1,9,10,ACC,-1,-1,-1},
	/*14*/{-1,-1,-1,106,-1,9,10,106,-1,-1,-1},
	/*15*/{-1,-1,-1,108,-1,9,10,108,-1,-1,-1}
};







//从文件读一行到缓冲区
void readline() {
	char ch1;
	pline = line;
	ch1 = getc(cfile);
	while (ch1 != '\n' && ch1 != EOF)
	{
		*pline = ch1;
		pline++;
		ch1 = getc(cfile);
	}
	*pline = '\0';
	pline = line;
}






//从缓冲区读取一个字符
void readch()
{
	if (ch == '\0')
	{
		readline();
		lnum++;
	}
	ch = *pline;
	pline++;
}





/********************** 变量匹配，查找变量名表 *******************/
int find(char spel[])
{
	int ss1 = 0;
	int ii = 0;
	while ((ss1 == 0) && (ii < nlength))
	{
		if (!strcmp(spel, ntab1[ii]))ss1 = 1;     /*查找，匹配*/
		ii++;

	}
	if (ss1 == 1)return ii - 1;                  /*查找到*/
	else return -1;                              /*没查找到*/
}





/********************* 标识符和保留字的识别 ***********************/
int identifier()
{
	int iii = 0, j, k;
	int ss = 0;
	k = 0;
	do {
		spelling[k] = ch;
		k++;
		readch();

	} while (((ch > 'a') && (ch < 'z')) || ((ch >= '0') && (ch <= '9')));
	pline--;
	spelling[k] = '\0';
	while ((ss == 0) && (iii < 10))
	{
		if (!strcmp(spelling, reswords[iii].sp))ss = 1;
		iii++;

	}
	//关键字匹配
	if (ss == 1)      //为保留关键字的情况
	{
		buf[count].sy1 = reswords[iii - 1].sy;     /*是保留字*/

	}
	else              //为变量的情况
	{    
		buf[count].sy1 = ident;                   /*是标识符，变量名*/
		j = find(spelling);
		if (j == -1)                              /*没有在变量名表中则添加*/
		{
			buf[count].pos = tt1;                 /*tt1是变量名表指针*/
			strcpy(ntab1[tt1], spelling);
			tt1++;
			nlength++;
		}
		else buf[count].pos = j;                  /*获得变量名自身的值*/ 
	}
	count++;
	for (k = 0; k < 10; k++)spelling[k] = ' ';    /*清空单词符号缓冲区*/
}





//数字识别
void number()
{
	int ivalue = 0;
	int digit;
	do
	{
		digit = ch - '0';
		ivalue = ivalue * 10 + digit;     /*数字字符转换为十进制整常数*/
		readch();
	} while ((ch >= '0') && (ch <= '9'));
	buf[count].sy1 = intconst;            /*整常数单词符号二元式*/
	buf[count].pos = ivalue;
	count++;
	pline--;
}



//扫描主函数
void scan()
{
	int i;
	while (ch != '~')
	{
		switch (ch)
		{
		case ' ':
			break;
		case 'a':
		case 'b':
		case 'c':
		case 'd':
		case 'e':
		case 'f':
		case 'g':
		case 'h':
		case 'i':
		case 'j':
		case 'k':
		case 'l':
		case 'm':
		case 'n':
		case 'o':
		case 'p':
		case 'q':
		case 'r':
		case 's':
		case 't':
		case 'u':
		case 'v':
		case 'w':
		case 'x':
		case 'y':
		case 'z':
			identifier();
			break;
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
			number();
			break;
		case '<':
			readch();
			if (ch == '=')
			{
				buf[count].pos = 0;   /*'<='标志*/
			}
			else
			{
				if (ch == '>') buf[count].pos = 4;   /*'<>'标志*/
				else
				{
					buf[count].pos = 1;  /*'<'标志*/
					pline--;
				}
			}
			buf[count].sy1 = rop;
			count++;
			break;
		case '>':
			readch();
			if (ch == '=')
			{
				buf[count].pos = 2;         /*'>='标志*/
			}
			else
			{
				buf[count].pos = 3;         /*'>'标志*/
				pline--;
			}
			buf[count].sy1 = rop;
			count++;
			break;
		case '(':
			buf[count].sy1 = lparent;
			count++;
			break;
		case ')':
			buf[count].sy1 = rparent;
			count++;
			break;
		case '#':
			buf[count].sy1 = jinghao;
			count++;
			break;
		case '+':
			buf[count].sy1 = plus;
			count++;
			break;
		case '*':
			buf[count].sy1 = times;
			count++;
			break;
		case ':':
			readch();
			if (ch == '=')
				buf[count].sy1 = becomes;    /* ':=' 标志*/
			count++;
			break;
		case '=':
			buf[count].sy1 = rop;            /* 关系运算标志*/
			buf[count].pos = 5;              /* '=' 标志*/
			count++;
			break;
		case ';':
			buf[count].sy1 = semicolon;
			count++;
			break;
		}
		readch();
	}
	buf[count].sy1 = -1;
}




/****************************************************************************/
void readnu()           /* 将buf中存储的二元式拷贝到n中 */
{
	if (pbuf->sy1 >= 0)
	{
		n.sy1 = pbuf->sy1;
		n.pos = pbuf->pos;
		pbuf++;
	}
}




/********************中间变量的生成***************************/
int newtemp()
{
	newt++;
	return newt;
}





/***********************生产四元式****************************/
int gen(const char op1[], struct aa arg11, struct aa arg22, int result1)
{
	strcpy(fexp[nxq].op, op1);
	fexp[nxq].arg1.sy1 = arg11.sy1;
	fexp[nxq].arg1.pos = arg11.pos;
	fexp[nxq].arg2.sy1 = arg22.sy1;
	fexp[nxq].arg2.pos = arg22.pos;
	fexp[nxq].result = result1;
	nxq++;
	return nxq - 1;
}





/********************布尔表达式的匹配**********************/
int merg(int p1, int p2)                                  /*拉链函数*/
{
	int p;
	if (p2 == 0) return p1;
	else
	{
		p = p2;
		while (fexp[p].result != 0) p = fexp[p].result;
		fexp[p].result = p1;
		return p2;
	}
}





void backpatch(int p, int t)                             /*返填函数*/
{
	int tempq;
	int q;
	q = p;
	while (q != 0)
	{
		tempq = fexp[q].result;
		fexp[q].result = t;
		q = tempq;
	}
}






/****************************************************/
int change1(int chan)
{
	switch (chan)
	{
	case ident:
	case intconst:
		return 0;
	case plus:
		return 1;
	case times:
		return 2;
	case lparent:
		return 3;
	case rparent:
		return 4;
	case jinghao:
		return 5;
	case tempsy:
		return 6;
	}
}

int change2(int chan)
{
	switch (chan)
	{
	case ident:
	case intconst:
		return 0;
	case rop:
		return 1;
	case lparent:
		return 2;
	case rparent:
		return 3;
	case op_not:
		return 4;
	case op_and:
		return 5;
	case op_or:
		return 6;
	case jinghao:
		return 7;
	case tempsy:
		return 8;
	case EA:
		return 9;
	case EO:
		return 10;

	}
}




/******************************赋值语句的分析*********************/
int lrparse1(int num)
{
	lr1 = action1[stack1[sp1]][change1(n1.sy1)];
	if (lr1 == -1)
	{
		printf("\n算式表达式或赋值语句出错\n");
		getchar();
		exit(0);
	}
	if ((lr1 < 10) && (lr1 >= 0))//移进
	{
		sp1++;
		stack1[sp1] = lr1;
		if (n1.sy1 != tempsy)
		{
			ssp++;
			num++;
			sstack[ssp].sy1 = n1.sy1;     /*将变量名压栈*/
			sstack[ssp].pos = n1.pos;     /*将变量名地址压栈*/ 

		}

		n1.sy1 = ibuf[num].sy1;
		n1.pos = ibuf[num].pos;
		lrparse1(num);
	}
	if ((lr1 >= 100) && (lr1 < 105))//归约
	{
		switch (lr1)//S'->E
		{
		case 100:
			break;
		case 101:
			E.pos = newtemp();//E->E+E
			gen("+", sstack[ssp - 2], sstack[ssp], E.pos + 100);
			ssp = ssp - 2;
			sstack[ssp].sy1 = tempsy;
			sstack[ssp].pos = E.pos;
			sp1 = sp1 - 3;
			break;
		case 102:
			E.pos = newtemp();
			gen("*", sstack[ssp - 2], sstack[ssp], E.pos + 100);
			ssp = ssp - 2;
			sstack[ssp].sy1 = tempsy;
			sstack[ssp].pos = E.pos;
			sp1 = sp1 - 3;
			break;
		case 103:
			E.pos = sstack[ssp - 1].pos;
			ssp = ssp - 2;
			sstack[ssp].sy1 = tempsy;
			sstack[ssp].pos = E.pos;
			sp1 = sp1 - 3;
			break;
		case 104:
			E.pos = sstack[ssp].pos;
			sp1--;
			break;
		}
		n1.sy1 = tempsy;
		n1.pos = E.pos;
		lrparse1(num);
	}

	if ((lr1 == ACC) && (stack1[sp1] == 1))
	{
		gen(":=", sstack[ssp], oth, ibuf[0].pos);
		ssp = ssp - 3;
		sp1 = sp1 - 3;

	}

}



/***************************布尔表达式的分析*********************/
int lrparse2(int num)
{
	int templabel;
	lr1 = action2[stack1[sp1]][change2(n1.sy1)];
	if (lr1 == -1)
	{
		if (sign == 2)printf("\n while 语句出错\n");
		if (sign == 3)printf("\n if 语句出错\n");
		getchar();
		exit(0);
	}
	if ((lr1 < 16) && (lr1 >= 0))//移进
	{
		sp1++;
		stack1[sp1] = lr1;
		ssp++;
		sstack[ssp].sy1 = n1.sy1;
		sstack[ssp].pos = n1.pos;
		if ((n1.sy1 != tempsy) && (n1.sy1 != EA) && (n1.sy1 != EO))
			num++;
		n1.sy1 = ibuf[num].sy1;
		n1.pos = ibuf[num].pos;
		lrparse2(num);

	}

	if ((lr1 >= 100) && (lr1 < 109))//归约
	{
		switch (lr1)
		{
		case 100:           //S'->B
			break;
		case 101:                      //B->i
			ntab2[label].tc = nxq;
			ntab2[label].fc = nxq + 1;
			gen("jnz", sstack[ssp], oth, 0);
			gen("j", oth, oth, 0);
			sp1--;
			ssp--;
			label++;
			n1.sy1 = tempsy;
			break;
		case 102:                        //B->i rop i
			ntab2[label].tc = nxq;
			ntab2[label].fc = nxq + 1;
			switch (sstack[ssp - 1].pos)
			{
			case 0:
				gen("j<=", sstack[ssp - 2], sstack[ssp], 0);
				break;
			case 1:
				gen("j<", sstack[ssp - 2], sstack[ssp], 0);
				break;
			case 2:
				gen("j>=", sstack[ssp - 2], sstack[ssp], 0);
				break;
			case 3:
				gen("j>", sstack[ssp - 2], sstack[ssp], 0);
				break;
			case 4:
				gen("j<>", sstack[ssp - 2], sstack[ssp], 0);
				break;
			case 5:
				gen("j=", sstack[ssp - 2], sstack[ssp], 0);
				break;


			}
			gen("j", oth, oth, 0);
			ssp = ssp - 3;
			sp1 = sp1 - 3;
			label++;
			n1.sy1 = tempsy;
			break;
		case 103:                 //B->(B)
			label = label - 1;
			ssp = ssp - 3;
			sp1 = sp1 - 3;
			label++;
			n1.sy1 = tempsy;
			break;
		case 104:                 //B->not B
			label = label - 1;
			templabel = ntab2[label].tc;
			ntab2[label].tc = ntab2[label].fc;
			ntab2[label].fc = templabel;
			ssp = ssp - 2;
			sp1 = sp1 - 2;
			label++;
			n1.sy1 = tempsy;
			break;
		case 105:                   //A->Band
			backpatch(ntab2[label - 1].tc, nxq);
			label = label - 1;
			ssp = ssp - 2;
			sp1 = sp1 - 2;
			label++;
			n1.sy1 = EA;
			break;
		case 106:                  //B->AB
			label = label - 2;
			ntab2[label].tc = ntab2[label + 1].tc;
			ntab2[label].fc = merg(ntab2[label].fc, ntab2[label + 1].fc);
			ssp = ssp - 2;
			sp1 = sp1 - 2;
			label++;
			n1.sy1 = tempsy;
			break;
		case 107:                     //O->B or
			backpatch(ntab2[label - 1].fc, nxq);
			label = label - 1;
			ssp = ssp - 2;
			sp1 = sp1 - 2;
			label++;
			n1.sy1 = EO;
			break;
		case 108:
			label = label - 2;
			ntab2[label].fc = ntab2[label + 1].fc;
			ntab2[label].tc = merg(ntab2[label].tc, ntab2[label + 1].tc);
			ssp = ssp - 2;
			sp1 = sp1 - 2;
			label++;
			n1.sy1 = tempsy;
			break;



		}
		lrparse2(num);


	}
	if (lr1 == ACC)return 1;

}




/******************************* 测试字符是否为表达式中的值,不包括";" *********************/
int test(int value)
{
	switch (value)
	{
	case intconst:
	case ident:
	case plus:
	case times:
	case becomes:
	case lparent:
	case rparent:
	case rop:
	case op_and:
	case op_or:
	case op_not:
		return 1;
	default:
		return 0;


	}

}



/********************************************/
int lrparse()                           /*程序语句处理*/
{
	int i1 = 0;
	int num = 0;
	/*指向表达式缓冲区*/
	if (test(n.sy1))                    
	{
		if (stack[sp].sy1 == sy_while) sign = 2;
		else
		{
			if (stack[sp].sy1 == sy_if) sign = 3;
			else sign = 1;
		}
		do
		{
			ibuf[i1].sy1 = n.sy1;
			ibuf[i1].pos = n.pos;
			readnu();
			i1++;
		} while (test(n.sy1));
		ibuf[i1].sy1 = jinghao;
		pbuf--;
		sstack[0].sy1 = jinghao;
		ssp = 0;
		if (sign == 1)
		{
			sp1 = 0;
			stack1[sp1] = 0;
			num = 2;
			n1.sy1 = ibuf[num].sy1;
			n1.pos = ibuf[num].pos;
			lrparse1(num);
			n.sy1 = a;
		}
		if ((sign == 2) || (sign == 3))
		{
			pointmark++;
			labelmark[pointmark].nxq1 = nxq;
			sp1 = 0;
			stack1[sp1] = 0;
			num = 0;
			n1.sy1 = ibuf[num].sy1;
			n1.pos = ibuf[num].pos;
			lrparse2(num);
			labelmark[pointmark].tc1 = ntab2[label - 1].tc;
			labelmark[pointmark].fc1 = ntab2[label - 1].fc;
			backpatch(labelmark[pointmark].tc1, nxq);
			n.sy1 = e;
		}
	}
	lr = action[stack[sp].pos][n.sy1];
	printf("stack[%d] = %d\t\tn = %d\t\tlr = %d\n", sp, stack[sp].pos, n.sy1, lr);
	if ((lr < 19 && (lr >= 0)))
	{
		sp++;
		stack[sp].pos = lr;
		stack[sp].sy1 = n.sy1;
		readnu();
		lrparse();
	}
	if ((lr <= 106) && (lr >= 100))      /*归约*/
	{
		switch (lr)
		{
		case 100:               /* S'->S */
			break;
		case 101:               /* S->if e than S else S */
			printf("S->if e than S else S归约\n");
			sp = sp - 6;
			n.sy1 = S;
			fexp[labeltemp[pointtemp]].result = nxq;
			pointtemp--;
			if (stack[sp].sy1 == sy_then)
			{
				gen("j", oth, oth, 0);
				backpatch(labelmark[pointmark].fc1, nxq);
				pointtemp++;
				labeltemp[pointtemp] = nxq - 1;
			}
			pointmark--;
			if (stack[sp].sy1 == sy_do)
			{
				gen("j", oth, oth, labelmark[pointmark].nxq1);
				backpatch(labelmark[pointmark].fc1, nxq);
			}
			break;
		case 102:               /* S->while e do S */
			printf("S->while e do S 归约\n");
			sp = sp - 4;
			n.sy1 = S;
			pointmark--;
			if (stack[sp].sy1 == sy_do)
			{
				gen("j", oth, oth, labelmark[pointmark].nxq1);
				backpatch(labelmark[pointmark].fc1, nxq);
			}

			if (stack[sp].sy1 == sy_then)
			{
				gen("j", oth, oth, 0);
				fexp[labelmark[pointmark].fc1].result = nxq;
				pointtemp++;
				labeltemp[pointtemp] = nxq - 1;
			}
			break;
		case 103:                /* S->begin L end */
			printf("S->begin L end归约\n");
			sp = sp - 3;
			n.sy1 = S;
			if (stack[sp].sy1 == sy_then)
			{
				gen("j", oth, oth, 0);
				backpatch(labelmark[pointmark].fc1, nxq);
				pointtemp++;
				labeltemp[pointtemp] = nxq - 1;
			}
			if (stack[sp].sy1 == sy_do)
			{
				gen("j", oth, oth, labelmark[pointmark].nxq1);
				backpatch(labelmark[pointmark].fc1, nxq);
			}
			getchar();
			break;
		case 104:                  /* S->a */
			printf("S->a归约\n");
			sp = sp - 1;
			n.sy1 = S;
			if (stack[sp].sy1 == sy_then)
			{
				gen("j", oth, oth, 0);
				backpatch(labelmark[pointmark].fc1, nxq);
				pointtemp++;
				labeltemp[pointtemp] = nxq - 1;
			}
			if (stack[sp].sy1 == sy_do)
			{
				gen("j", oth, oth, labelmark[pointmark].nxq1);
				backpatch(labelmark[pointmark].fc1, nxq);
			}
			break;
		case 105:               /* L -> S */
			printf("L->S归约\n");
			sp = sp - 1;
			n.sy1 = L;
			break;
		case 106:              /* L->S;L */
			printf("L->S;L归约\n");
			sp = sp - 3;
			n.sy1 = L;
			break;
		}
		getchar();
		pbuf--;
		lrparse();
	}
	if (lr == ACC) return ACC;
}
/*************************  disp1  *************************/
void disp1()
{
	int temp1 = 0;
	printf("\n************ 词法分析结果 ****************\n");
	for (temp1 = 0; temp1 < count; temp1++)
	{
		printf("%d\t %d\t \n", buf[temp1].sy1, buf[temp1].pos);
		if (temp1 == 20)
		{
			printf("Press any key to continue ... \n");
			getchar();
		}
	}
	getchar();
}
/*******************************************************/
void disp2()
{
	int temp1 = 100;
	printf("\n************** 四元式分析结果 ******************\n");
	for (temp1 = 100; temp1 < nxq; temp1++)
	{
		printf("%d\t", temp1);
		printf("(%s\t,", fexp[temp1].op);
		if (fexp[temp1].arg1.sy1 == ident)
			printf("%s\t,", ntab1[fexp[temp1].arg1.pos]);
		else
		{
			if (fexp[temp1].arg1.sy1 == tempsy)
				printf("T%d\t,", fexp[temp1].arg1.pos);
			else
			{
				if (fexp[temp1].arg1.sy1 == intconst)
					printf("%d\t,", fexp[temp1].arg1.pos);
				else printf("\t,");
			}
		}
		if (fexp[temp1].arg2.sy1 == ident)
			printf("%s\t,", ntab1[fexp[temp1].arg1.pos]);
		else
		{
			if (fexp[temp1].arg2.sy1 == tempsy)
				printf("T %d\t,", fexp[temp1].arg2.pos);
			else
			{
				if (fexp[temp1].arg2.sy1 == intconst)
					printf("%d\t,", fexp[temp1].arg2.pos);
				else printf("\t,");
			}
		}
		if (fexp[temp1].op[0] != 'j')
		{
			if (fexp[temp1].result >= 100)
				printf("T%d\t)", fexp[temp1].result - 100);
			else
				printf("%s\t)", ntab1[fexp[temp1].result]);
		}
		else printf("%d\t)", fexp[temp1].result);
		if (temp1 == 20)
		{
			printf("\n Press any key to continue ... \n");
			getchar();
		}
		printf("\n");
	}
	getchar();
}
void disp3()
{
	int tttt;
	printf("\n\n 程序总共 %d 行,产生了 %d 个二元式！ \n", lnum, count);
	getchar();
	printf("\n **************** 变量名表 ****************** \n");
	for (tttt = 0; tttt < tt1; tttt++)
		printf("%d\t %s\n", tttt, ntab1[tttt]);
	getchar();
}
/********************* 主程序 ****************/
void main()
{
	cfile = fopen("D:\\pas.txt", "r");                      /*打开C语言源文件*/
	readch();                                           /*从源文件读一个字符*/
	scan();                                             /*词法分析*/
	disp1();
	disp3();
	stack[sp].pos = 0;
	stack[sp].sy1 = -1;                                /*初始化状态栈*/
	stack1[sp1] = 0;                                   /*初始化状态栈1*/
	oth.sy1 = -1;
	printf("\n********** 状态栈加工过程及规约顺序 **************** \n");
	readnu();                                         /*从二元式读入一个字符*/

	lrparse();                                        /*四元式分析*/
	getchar();
	disp2();
	printf("\n 程序运行结束！ \n");
	getchar();
}
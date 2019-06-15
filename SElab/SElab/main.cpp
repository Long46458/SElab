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
char ch = '\0';                      /* ���ַ���������ȡ��ǰ�ַ� */
int count = 0;                       /* �ַ����� */
static char spelling[10] = { "" };   /* ���ʶ��ĵ��ʷ��� */
static char line[81] = { "" };       /* �л����� */
char* pline;                         /* �ַ�������ָ�� */
static char ntab1[100][10];          /* ����������100�ÿ���10 */
struct ntab
{
	int tc;              /*��ֵ*/
	int fc;              /*��ֵ*/

}ntab2[200];             /*�ڲ������ʽE�б����йز����������桢��ֵ*/

int label = 0;           /*ָ��ntab2��ָ��*/

struct rwords {
	char sp[10];        /*������*/
	int sy;             /*�������������*/
};                      /*�����ֱ�Ľṹ�����������뻺�����еĵ��ʽ���ƥ��*/



struct rwords reswords[10] = { {"if",sy_if},{"do",sy_do},{"else",sy_else},{"while",sy_while},{"then",sy_then},{"begin",sy_begin},{"end",sy_end},{"and",op_and},{"or",op_or},{"not",op_not} };



struct aa {
	int sy1;            /*��ŵ��ʷ��ŵ��ֱ����*/ 
	int pos;            /*��ŵ��ʷ��������ֵ*/

}buf[1000],/*�ʷ��������������������ʶ������ĵ��ʷ���*/
 n, /*��ȡ��Ԫʽ�ĵ�ǰ����*/  
 n1,/*��ǰ���ʽ�еķ���*/ 
 E,/*���ս��*/
 sstack[100],/*�����򲼶����ʽ�ӹ�����ʹ�õķ���ջ*/
 ibuf[100],/*�����򲼶����ʽʹ�õĻ�����*/ 
 stack[1000];/*�﷨�����ӹ�����ʹ�õķ���ջ*/





struct aa oth;         /*��Ԫʽ�еĿհ�λ��*/
struct fourexp {
	char op[10];
	struct aa arg1;
	struct aa arg2;
	int result;

}fexp[200];                /*��Ԫʽ�Ľṹ����*/ 

int ssp = 0;               /*ָ��sstackջָ��*/
struct aa *pbuf = buf;     /*ָ��ʷ�������������ָ��*/
int nlength = 0;           /*�ʷ������м�¼���ʵĳ���*/
int lnum = 0;              /*Դ������������*/
int tt1 = 0;               /*��������ָ��*/
FILE* cfile;               /*Դ�����ļ���~Ϊ������*/






/***********************************/
int newt = 0;             /*��ʱ����������*/
int nxq = 100;            /*nxq����ָ����һ����Ҫ�γɵ���Ԫʽ��ַ��*/
int lr;                   /*ɨ��LR������1�����б���ĵ�ǰ״ֵ̬*/
int lr1;                  /*ɨ��LR������2���3������ĵ�ǰ״ֵ̬*/
int sp = 0;               /*����LR������ʱ״̬ջ��ջ��ָ��*/
int stack1[100];          /*״̬ջ1����*/
int sp1 = 0;              /*״̬ջ1��ջ��ָ��*/
int num = 0;              /*�����򲼶����ʽ������ָ��*/
struct ll {
	int nxq1;             /*��¼��һ����Ԫʽ�ĵ�ַ*/
	int tc1;              /*��ֵ��*/
	int fc1;              /*��ֵ��*/

}labelmark[10];           /*��¼���Ƕ�ײ�ε����飬����¼Ƕ����ÿ��Ĳ������ʽE���׵�ַ*/




int labeltemp[10];       /*��¼���Ƕ�ײ�ε����飬����¼ÿ��else֮ǰ����Ԫʽ��ַ*/
int pointmark = -1,/*labelmark����ָ��*/ pointtemp = -1; /*labeltemp����ָ��*/
int sign = 0;            /*sign=1Ϊ��ֵ��䣻=2Ϊwhile��䣻=3Ϊif���*/ 





/***********��������LR������*******************/

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





/*�������ʽ��LR������*/
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





//�������ʽ��LR������
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







//���ļ���һ�е�������
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






//�ӻ�������ȡһ���ַ�
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





/********************** ����ƥ�䣬���ұ������� *******************/
int find(char spel[])
{
	int ss1 = 0;
	int ii = 0;
	while ((ss1 == 0) && (ii < nlength))
	{
		if (!strcmp(spel, ntab1[ii]))ss1 = 1;     /*���ң�ƥ��*/
		ii++;

	}
	if (ss1 == 1)return ii - 1;                  /*���ҵ�*/
	else return -1;                              /*û���ҵ�*/
}





/********************* ��ʶ���ͱ����ֵ�ʶ�� ***********************/
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
	//�ؼ���ƥ��
	if (ss == 1)      //Ϊ�����ؼ��ֵ����
	{
		buf[count].sy1 = reswords[iii - 1].sy;     /*�Ǳ�����*/

	}
	else              //Ϊ���������
	{    
		buf[count].sy1 = ident;                   /*�Ǳ�ʶ����������*/
		j = find(spelling);
		if (j == -1)                              /*û���ڱ��������������*/
		{
			buf[count].pos = tt1;                 /*tt1�Ǳ�������ָ��*/
			strcpy(ntab1[tt1], spelling);
			tt1++;
			nlength++;
		}
		else buf[count].pos = j;                  /*��ñ����������ֵ*/ 
	}
	count++;
	for (k = 0; k < 10; k++)spelling[k] = ' ';    /*��յ��ʷ��Ż�����*/
}





//����ʶ��
void number()
{
	int ivalue = 0;
	int digit;
	do
	{
		digit = ch - '0';
		ivalue = ivalue * 10 + digit;     /*�����ַ�ת��Ϊʮ����������*/
		readch();
	} while ((ch >= '0') && (ch <= '9'));
	buf[count].sy1 = intconst;            /*���������ʷ��Ŷ�Ԫʽ*/
	buf[count].pos = ivalue;
	count++;
	pline--;
}



//ɨ��������
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
				buf[count].pos = 0;   /*'<='��־*/
			}
			else
			{
				if (ch == '>') buf[count].pos = 4;   /*'<>'��־*/
				else
				{
					buf[count].pos = 1;  /*'<'��־*/
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
				buf[count].pos = 2;         /*'>='��־*/
			}
			else
			{
				buf[count].pos = 3;         /*'>'��־*/
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
				buf[count].sy1 = becomes;    /* ':=' ��־*/
			count++;
			break;
		case '=':
			buf[count].sy1 = rop;            /* ��ϵ�����־*/
			buf[count].pos = 5;              /* '=' ��־*/
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
void readnu()           /* ��buf�д洢�Ķ�Ԫʽ������n�� */
{
	if (pbuf->sy1 >= 0)
	{
		n.sy1 = pbuf->sy1;
		n.pos = pbuf->pos;
		pbuf++;
	}
}




/********************�м����������***************************/
int newtemp()
{
	newt++;
	return newt;
}





/***********************������Ԫʽ****************************/
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





/********************�������ʽ��ƥ��**********************/
int merg(int p1, int p2)                                  /*��������*/
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





void backpatch(int p, int t)                             /*�����*/
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




/******************************��ֵ���ķ���*********************/
int lrparse1(int num)
{
	lr1 = action1[stack1[sp1]][change1(n1.sy1)];
	if (lr1 == -1)
	{
		printf("\n��ʽ���ʽ��ֵ������\n");
		getchar();
		exit(0);
	}
	if ((lr1 < 10) && (lr1 >= 0))//�ƽ�
	{
		sp1++;
		stack1[sp1] = lr1;
		if (n1.sy1 != tempsy)
		{
			ssp++;
			num++;
			sstack[ssp].sy1 = n1.sy1;     /*��������ѹջ*/
			sstack[ssp].pos = n1.pos;     /*����������ַѹջ*/ 

		}

		n1.sy1 = ibuf[num].sy1;
		n1.pos = ibuf[num].pos;
		lrparse1(num);
	}
	if ((lr1 >= 100) && (lr1 < 105))//��Լ
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



/***************************�������ʽ�ķ���*********************/
int lrparse2(int num)
{
	int templabel;
	lr1 = action2[stack1[sp1]][change2(n1.sy1)];
	if (lr1 == -1)
	{
		if (sign == 2)printf("\n while ������\n");
		if (sign == 3)printf("\n if ������\n");
		getchar();
		exit(0);
	}
	if ((lr1 < 16) && (lr1 >= 0))//�ƽ�
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

	if ((lr1 >= 100) && (lr1 < 109))//��Լ
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




/******************************* �����ַ��Ƿ�Ϊ���ʽ�е�ֵ,������";" *********************/
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
int lrparse()                           /*������䴦��*/
{
	int i1 = 0;
	int num = 0;
	/*ָ����ʽ������*/
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
	if ((lr <= 106) && (lr >= 100))      /*��Լ*/
	{
		switch (lr)
		{
		case 100:               /* S'->S */
			break;
		case 101:               /* S->if e than S else S */
			printf("S->if e than S else S��Լ\n");
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
			printf("S->while e do S ��Լ\n");
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
			printf("S->begin L end��Լ\n");
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
			printf("S->a��Լ\n");
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
			printf("L->S��Լ\n");
			sp = sp - 1;
			n.sy1 = L;
			break;
		case 106:              /* L->S;L */
			printf("L->S;L��Լ\n");
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
	printf("\n************ �ʷ�������� ****************\n");
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
	printf("\n************** ��Ԫʽ������� ******************\n");
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
	printf("\n\n �����ܹ� %d ��,������ %d ����Ԫʽ�� \n", lnum, count);
	getchar();
	printf("\n **************** �������� ****************** \n");
	for (tttt = 0; tttt < tt1; tttt++)
		printf("%d\t %s\n", tttt, ntab1[tttt]);
	getchar();
}
/********************* ������ ****************/
void main()
{
	cfile = fopen("D:\\pas.txt", "r");                      /*��C����Դ�ļ�*/
	readch();                                           /*��Դ�ļ���һ���ַ�*/
	scan();                                             /*�ʷ�����*/
	disp1();
	disp3();
	stack[sp].pos = 0;
	stack[sp].sy1 = -1;                                /*��ʼ��״̬ջ*/
	stack1[sp1] = 0;                                   /*��ʼ��״̬ջ1*/
	oth.sy1 = -1;
	printf("\n********** ״̬ջ�ӹ����̼���Լ˳�� **************** \n");
	readnu();                                         /*�Ӷ�Ԫʽ����һ���ַ�*/

	lrparse();                                        /*��Ԫʽ����*/
	getchar();
	disp2();
	printf("\n �������н����� \n");
	getchar();
}
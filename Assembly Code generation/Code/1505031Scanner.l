
%option noyywrap
%x comment comment2 MULTILINESTRING
%{

#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<iterator>
#include<vector>
#include<cstring>
#include<iostream>
#include"1505031_SymbolTable.h"
#include "y.tab.h"

using namespace std;

extern YYSTYPE yylval;
extern SymbolTable table;
extern ofstream errout;
extern int line_count;

extern int lexical_errors;
void yyerror(char *);



int len;
char *commentStr;
int commentLineNo;
int stringLineNo;
string commentnew;
FILE *tokenout;
/*void eat_to_newline(void){
int c;
while((c=getchar())!=EOF && c!= '\n') ;
}*/
void IncEc(){
    lexical_errors++;
}
void StringParsing() {
        int i;
        yyleng--;
        char *yycopy = strdup( yytext );
        char arr[yyleng-1];
        int j=0;
        int backslash = 0;
        for ( i = 1; i <yyleng;i++ ) {
	if(yycopy[i]=='"') {
        arr[j] = yycopy[i];
        j++;
        continue;
        }
	if(yycopy[i]=='\n') line_count++;
        if(yycopy[i]=='\\'&&yycopy[i-1]!='\\') {backslash=1;continue;}
	if(backslash ==0)  {
        arr[j] = yycopy[i];
        j++;
        }
        else 
        {
        char c;
        if(yycopy[i]=='n') {
        c = '\n';
        arr[j] = c;
        j++;
        }
        else if(yycopy[i]=='t') {
        c = '\t';
        arr[j] = c;
        j++;
        }
        else if(yycopy[i]=='a') {
        c = '\a';
        arr[j] = c;
        j++;
        }
        else if(yycopy[i]=='f') {
        c = '\f';
        arr[j] = c;
        j++;
        }
        else if(yycopy[i]=='r') {
        c = '\r';
        arr[j] = c;
        j++;
        }
        else if(yycopy[i]=='b') {
        c = '\b';
        arr[j] = c;
        j++;
        }
        else if(yycopy[i]=='v') {
        c = '\v';
        arr[j] = c;
        j++;
        }
        else if(yycopy[i]=='0') {
        c = '\0';
        arr[j] = c;
        j++;
        }
        else if(yycopy[i]=='\\') {
        c = '\\';
        arr[j] = c;
        j++;
        }
        
        
        backslash=0;
        }
        }
        arr[j] = '\0';
        j++;
        char arrnew[j];
        for (int k=0;k<j;k++) {arrnew[k]=arr[k];}
          
    free( yycopy );
    
        }
void UnStringParsing() {
        int i;

        yyleng--;
        char *yycopy = strdup( yytext );
        char arr[yyleng-1];
        int j=0;
        int backslash = 0;
        
        for ( i = 1; i <yyleng;i++ ) {
	if(yycopy[i]=='\n') line_count++;}
       
        
    free( yycopy );
    
        }

    
        

%}

WHITESPACE [ \t\f\r\v]+ 
LETTER [a-zA-Z]
LETTERS [a-zA-Z]+
DIGIT [0-9]
DIGITS [0-9]+
ID      ({LETTER}|_)({LETTER}|{DIGIT}|_)*
HEXA "0X"[0-9a-fA-F]+
INVALIDID [0-9]+({LETTER}|_)({LETTER}|{DIGIT}|_)*
STRING ["]([^"\\\n]|\\.|\\\n)*["]
CONSTCHAR "'"([a-zA-Z]|\\[ntafrbv0]|\\\\|\\'')"'"
CONSTFLOAT [0-9]*(\.[0-9]+)?(E[+-]?[0-9]+)?
ILLFORMEDNUMBER [0-9]*(\.[0-9]*)?(E[+-]?[0-9]*\.[0-9]*)?
TOOMANYDECIMALPOINTS ([0-9]+\.)+[0-9]*
MULTICHAR "'"([a-zA-Z]|" "|\\[ntafrbv0]|\\\\|\\'')+"'"
SPECIALSYMBOL (\\n|\\t|\\\|\\a|\\f|\\r|\\b|\\v|\\0|\\')
UNFINISHEDCHAR "'"([a-zA-Z]|\\[ntafrbv0]|\\\\|\\''|\\)?[']?    
EMPTYCHAR "'"+"'"
UNFINISHEDSTRING ["]([^"\\\n]|\\.|\\\n)*
UNRECOGNIZEDCHAR (.)
NEWLINE \n
doubleq \"

%%
{WHITESPACE} {    }
{NEWLINE} {     line_count++;}


	"if"    {
                
	    return IF;
        }
        
	"else"    {
    
	   return ELSE;
        }
        "for"    {
    
	    return FOR;
        }
        "while"    {
    
	return WHILE;
	    
}
	"do"    {
    
	return DO;
        }
        "break"        {
    
	return BREAK;
        }
        "int"    {
    
return INT;
        }
        "char"    {
    
return CHAR;
        }
        "float"    {
    
return FLOAT;
        }
        "double"    {
    
return DOUBLE;
        }
        "void"    {
    
return VOID;
        }
        "return"    {
    
return RETURN;
        }
        "switch"    {
    
return SWITCH;
        }
        "case"    {
    
return CASE;
        }
        "default"    {
    
return DEFAULT;
        }
        "continue"    {
    
return CONTINUE;
        }
        "println"       {
            return PRINTLN;
        }


        "+"|"-"        {
    
SymbolInfo *s= new  SymbolInfo(yytext, (char *)"ADDOP");
			yylval = (YYSTYPE)s;
            return ADDOP;
        }
        
        "*"|"/"|"%"    {
    
SymbolInfo *s= new  SymbolInfo(yytext, (char *)"MULOP");
			yylval = (YYSTYPE)s;
            return MULOP;
           
                }
                
        "++"    {
    
SymbolInfo *s= new  SymbolInfo(yytext, (char *)"INCOP");
			yylval = (YYSTYPE)s;
            return INCOP;
           
                }
	"--"    {
    
SymbolInfo *s= new  SymbolInfo(yytext, (char *)"DECOP");
			yylval = (YYSTYPE)s;
            return DECOP;
           
                }
        "<"|"<="|">"|">="|"=="|"!="   {
    
           SymbolInfo *s= new  SymbolInfo(yytext, (char *)"RELOP");
			yylval = (YYSTYPE)s;
            return RELOP;
        
                
        }
        "="            {
    
SymbolInfo *s= new  SymbolInfo(yytext, (char *)"ASSIGNOP");
			yylval = (YYSTYPE)s;
            return ASSIGNOP;
        
        
        }
        "&&"|"||"        {
    
SymbolInfo *s= new  SymbolInfo(yytext, (char *)"LOGICOP");
			yylval = (YYSTYPE)s;
            return LOGICOP;
           
        
        }
        "&"|"|"|"^"|"<<"|">>"    {
    
SymbolInfo *s= new  SymbolInfo(yytext, (char *)"BITOP");
			yylval = (YYSTYPE)s;
            return BITOP;
         
        }
        "!"        {
    

            return NOT;
         
        }
        "("        {
    
	return LPAREN;
           
        }
        ")"        {
    
	return RPAREN;
            
        }
        "{"        {
    

	return LCURL;
         
         
        }
        "}"        {
    
	return RCURL;
           
        }
        "["        {
    
 return LTHIRD;
            
        }
        "]"        {
    
 return RTHIRD;
            
        }
        ","        {
    
 return COMMA;
       
        }
        ";"        {
    
 return SEMICOLON;
        }
            
            
            [0-9]+    {
    

                SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_INT");
				yylval = (YYSTYPE)s;
				return CONST_INT;
            }
            {CONSTFLOAT} {
    
        
        SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_FLOAT");
				yylval = (YYSTYPE)s;
			//yylval.dval = atof(yytext);
				return CONST_FLOAT; 
        }
        
        {CONSTCHAR}    {
    
        
        int i;
        yyleng--;
        char *yycopy = strdup( yytext );
        char separatedChar[3];
        int backslash = 0;
        for ( i = 1; i <yyleng;i++ ) {
        if(yycopy[i]=='\\'&&yycopy[i-1]!='\\') {backslash=1;continue;}
        if(backslash ==0)  {
        char c = yycopy[i];
        char str1[2] = {c , '\0'};
     SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        
        }
        else 
        {
        char c;
        if(yycopy[i]=='n') {
	
        c = '\n';
        //printf("%c ",c);
	char separated[3] = {'\\','n','\0'};
        char str1[2] = {c , '\0'};
   SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
        else if(yycopy[i]=='t') {
        c = '\t';
        //printf("%c ",c);
char separated[3] = {'\\','t','\0'};
        char str1[2] = {c , '\0'};
        
 SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
        else if(yycopy[i]=='a') {
        c = '\a';
        //printf("%c ",c);
char separated[3] = {'\\','a','\0'};
        char str1[2] = {c , '\0'};
 SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
        else if(yycopy[i]=='f') {
        c = '\f';
        //printf("%c ",c);
char separated[3] = {'\\','f','\0'};
        char str1[2] = {c , '\0'};
        
 SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
        else if(yycopy[i]=='r') {
        c = '\r';
char separated[3] = {'\\','r','\0'};
        char str1[2] = {c , '\0'};
        
 SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
        else if(yycopy[i]=='b') {
        c = '\b';
        //printf("%c ",c);
char separated[3] = {'\\','b','\0'};
        char str1[2] = {c , '\0'};
 SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
        else if(yycopy[i]=='v') {
        c = '\v';
        //printf("%c ",c);
char separated[3] = {'\\','v','\0'};
        char str1[2] = {c , '\0'};
 SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
        else if(yycopy[i]=='0') {
        c = '\0';
char separated[3] = {'\\','0','\0'};
        char str1[2] = {c , '\0'};
        
 SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
        else if(yycopy[i]=='\\') {
        c = '\\';
        //printf("%c ",c);
char separated[3] = {'\\','\\','\0'};
        char str1[2] = {c , '\0'};
        
 SymbolInfo *s= new  SymbolInfo(yytext, (char *)"CONST_CHAR");
				yylval = (YYSTYPE)s;
				return CONST_CHAR; 
        }
   
        
        backslash=0;
        }
        }   
    free( yycopy );
            }
            
            
        {STRING}    {
        stringLineNo = line_count;
        StringParsing();
         
        } 
        
        
        
        
        {ID}  {
      
	SymbolInfo *s= table.LookUp(yytext);

				if(s==NULL)
				{			
					s= new SymbolInfo(yytext, (char *)"ID");
				}
				yylval = (YYSTYPE)s;			
				return ID;
        
        }

        
        
        
       

         


        "/*"         {
commentnew.clear();
        //printf("\n COMMENT started at %s\n",yytext);
        commentLineNo = line_count;
        BEGIN(comment);
        string temp(yytext);
	commentnew=commentnew+temp;
        }

<comment>[^*\n]*        {
string temp(yytext);
	commentnew=commentnew+temp;

}
<comment>"*"+[^*/\n]*  {
string temp(yytext);
	commentnew=commentnew+temp;
}


<comment>(\n)       {
++line_count;
string temp(yytext);
	commentnew=commentnew+temp;
}

<comment>"*"+"/"       {
string temp(yytext);
	commentnew=commentnew+temp;
len = commentnew.size();
  char *str=new char[len+1];
std::copy(commentnew.begin(),commentnew.end(),str);
str[len]='\0';
commentnew.clear();
 BEGIN(INITIAL);
 }




        "//"         {
        commentLineNo = line_count;
        BEGIN(comment2);
        string temp(yytext);
	commentnew=commentnew+temp;
	//cout << commentnew;
        }

<comment2>(\\\n)        {
++line_count;
       string temp(yytext);
	commentnew=commentnew+temp;
	//cout << commentnew;
}
<comment2>{WHITESPACE} {
       string temp(yytext);
	commentnew=commentnew+temp;
	//cout << commentnew;
}
<comment2>({LETTERS}|{DIGITS}|{SPECIALSYMBOL})*     {
       string temp(yytext);
	commentnew=commentnew+temp;
	//cout << commentnew;

}
<comment2>(\n)           {
     ++line_count;
       int len = commentnew.size();
       char *str=new char[len+1];
std::copy(commentnew.begin(),commentnew.end(),str);
str[len]='\0';
//cout << "final comment:   " << commentnew;

BEGIN(INITIAL);
////fprintf(logout,"Line no %d: TOKEN <COMMENT> Lexeme %s found\n",commentLineNo,str);

commentnew.clear();
}
        
        
        {INVALIDID} {
        IncEc();

       errout << "Error at Line no " << line_count << " INVALID IDENTIFIER found " << yytext << endl;
        ////printf("\nINVALID IDENTIFIER FOUND\n");
        }
        {ILLFORMEDNUMBER} {
        IncEc();
        errout << "Error at Line no " << line_count << " ILLFORMED NUMBER FOUND " << yytext << endl;
       
        ////fprintf(logout,"Error at Line no %d: ILLFORMED NUMBER found %s\n",line_count,yytext);
        ////printf("\nILLFORMED NUMBER FOUND\n");
        }
        {TOOMANYDECIMALPOINTS} {
        IncEc();
        errout << "Error at Line no " << line_count << "TOO MANY DECIMAL POINTS found " << yytext << endl;
       

        ////fprintf(logout,"Error at Line no %d: TOO MANY DECIMAL POINTS found %s\n",line_count,yytext);
        ////printf("\nTOO MANY DECIMAL POINTS FOUND\n");
        }
        {MULTICHAR} {
        IncEc();
        errout << "Error at Line no " << line_count << " MULTICHARACTER CONSTANT ERROR found " << yytext << endl;
       
        ////fprintf(logout,"Error at Line no %d: MULTICHARACTER CONSTANT ERROR found %s\n",line_count,yytext);
        ////printf("\nMULTICHARACTER CONSTANT ERROR FOUND\n");
        }
        {EMPTYCHAR} {
            errout << "Error at Line no " << line_count << " EMPTY CHARACTER found" << yytext << endl;
       
        IncEc();
        ////fprintf(logout,"Error at Line no %d: EMPTY CHARACTER found %s\n",line_count,yytext);
        ////printf("\nEMPTY CHARACTER FOUND\n");
        }
        
        {UNFINISHEDCHAR} {
            errout << "Error at Line no " << line_count << "UNFINISHED CHARACTER found " << yytext << endl;
       
        IncEc();
        ////fprintf(logout,"Error at Line no %d: UNFINISHED CHARACTER found %s\n",line_count,yytext);
        ////printf("\nUNFINISHED CHARACTER FOUND\n");
        }
        {UNFINISHEDSTRING} {
        IncEc();
errout << "Error at Line no " << line_count << " NEW UNFINISHED STRING FOUND" << yytext << endl;
       
        ////fprintf(logout,"Error at Line no %d: UNFINISHED STRING found %s\n",line_count,yytext);
	UnStringParsing();
        //printf("\nNEW UNFINISHED STRING FOUND %s\n",yytext);
        }
 	{UNRECOGNIZEDCHAR} {
        IncEc();
errout << "Error at Line no " << line_count << " UNRECOGNIZED CHARACTER FOUND " << yytext << endl;
       
        ////fprintf(logout,"Error at Line no %d: UNRECOGNIZED CHARACTER found %s\n",line_count,yytext);
 
        }
        
        
                 
        
        
        <comment><<EOF>> {
			line_count--;
       		        IncEc();
                        len = commentnew.size();
      		        char *str=new char[len+1];
			std::copy(commentnew.begin(),commentnew.end(),str);
			str[len]='\0';
			//cout << "unfinished final comment:   " << commentnew;
                      errout << "Error at Line no " << line_count << " UNFINISHED COMMENT FOUND " << yytext << endl;
       
                        ////fprintf(logout,"Error at Line no %d: UNFINISHED COMMENT found %s\n",commentLineNo,str);
			
                        ////fprintf(logout,"Total Line Number: %d and error : %d\n",line_count,lexical_errors); 
			commentnew.clear();
                        yyterminate();
                        //printf("Total Line Number: %d and error : %d\n",line_count,lexical_errors); 
                        return 0;
                        }
                    
                        <<EOF>> {
			line_count--;
                        //printf("Total Line Number: %d and error: %d\n",line_count,lexical_errors); 
                        ////fprintf(logout,"Total Line Number: %d and error : %d\n",line_count,lexical_errors); 
                        return 0;
                        }
        
    
        
        
            
        

            

%%

//int yywrap(void){return 1;}



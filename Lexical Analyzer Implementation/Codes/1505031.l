
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
using namespace std;
int line_count=1;
int error_count=0;
int word_count = 0;
SymbolTable table(50);
int len;
char *commentStr;
int commentLineNo;
int stringLineNo;
string commentnew;
FILE *tokenout;
void IncWc(){
    word_count++;
}
void IncEc(){
    error_count++;
}
void StringParsing() {
        int i;
        yyleng--;
        char *yycopy = strdup( yytext );
        char arr[yyleng-1];
        int j=0;
        int backslash = 0;
         //printf("in single line characters are parsed: ");
        
        for ( i = 1; i <yyleng;i++ ) {
        //printf("before: %c after:",yycopy[i]);
	if(yycopy[i]=='"') {
        arr[j] = yycopy[i];
        j++;
        //printf("%c",yycopy[i]);
        continue;
        }
	if(yycopy[i]=='\n') line_count++;
        if(yycopy[i]=='\\'&&yycopy[i-1]!='\\') {backslash=1;continue;}
	if(backslash ==0)  {
        arr[j] = yycopy[i];
        j++;
        //printf("%c",yycopy[i]);
        }
        else 
        {
        char c;
        if(yycopy[i]=='n') {
        c = '\n';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        else if(yycopy[i]=='t') {
        c = '\t';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        else if(yycopy[i]=='a') {
        c = '\a';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        else if(yycopy[i]=='f') {
        c = '\f';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        else if(yycopy[i]=='r') {
        c = '\r';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        else if(yycopy[i]=='b') {
        c = '\b';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        else if(yycopy[i]=='v') {
        c = '\v';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        else if(yycopy[i]=='0') {
        c = '\0';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        else if(yycopy[i]=='\\') {
        c = '\\';
        arr[j] = c;
        j++;
        //printf("%c",c);
        }
        
        
        backslash=0;
        }
        }
        arr[j] = '\0';
        j++;
        char arrnew[j];
        for (int k=0;k<j;k++) {arrnew[k]=arr[k];}
        
    //printf("\nparsing is done-- %s\n",arrnew);    
    free( yycopy );
    
        fprintf(tokenout,"<STRING,%s>",arrnew);
        fprintf(logout,"Line no %d: TOKEN <STRING> Lexeme %s found\n",stringLineNo,arrnew);
        }
void UnStringParsing() {
        int i;
        //printf("before, %s----",yytext);

        yyleng--;
        char *yycopy = strdup( yytext );
        char arr[yyleng-1];
        int j=0;
        int backslash = 0;
         //printf("in single line characters are parsed: ");
        
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
{WHITESPACE} {}
{NEWLINE} {line_count++;}


"if"    {
            fprintf(tokenout,"<IF>");
            fprintf(logout,"Line no %d: TOKEN <IF> Lexeme %s found\n",line_count,yytext);
        }
        
"else"    {
            fprintf(tokenout,"<ELSE>");
            fprintf(logout,"Line no %d: TOKEN <ELSE> Lexeme %s found\n",line_count,yytext);
        }
        "for"    {
            fprintf(tokenout,"<FOR>");
            fprintf(logout,"Line no %d: TOKEN <FOR> Lexeme %s found\n",line_count,yytext);
        }
"while"    {
            fprintf(tokenout,"<WHILE>");
            fprintf(logout,"Line no %d: TOKEN <WHILE> Lexeme %s found\n",line_count,yytext);
}
"do"    {
            fprintf(tokenout,"<DO>");
            fprintf(logout,"Line no %d: TOKEN <DO> Lexeme %s found\n",line_count,yytext);
        }
        "break"        {
            fprintf(tokenout,"<BREAK>");
            fprintf(logout,"Line no %d: TOKEN <BREAK> Lexeme %s found\n",line_count,yytext);
        }
        "int"    {
            fprintf(tokenout,"<INT>");
            fprintf(logout,"Line no %d: TOKEN <INT> Lexeme %s found\n",line_count,yytext);
        }
        "char"    {
            fprintf(tokenout,"<CHAR>");
            fprintf(logout,"Line no %d: TOKEN <CHAR> Lexeme %s found\n",line_count,yytext);
        }
        "float"    {
            fprintf(tokenout,"<FLOAT>");
            fprintf(logout,"Line no %d: TOKEN <FLOAT> Lexeme %s found\n",line_count,yytext);
        }
        "double"    {
            fprintf(tokenout,"<DOUBLE>");
            fprintf(logout,"Line no %d: TOKEN <DOUBLE> Lexeme %s found\n",line_count,yytext);
        }
        "void"    {
            fprintf(tokenout,"<VOID>");
            fprintf(logout,"Line no %d: TOKEN <VOID> Lexeme %s found\n",line_count,yytext);
        }
        "return"    {
            fprintf(tokenout,"<RETURN>");
            fprintf(logout,"Line no %d: TOKEN <RETURN> Lexeme %s found\n",line_count,yytext);
        }
        "switch"    {
            fprintf(tokenout,"<SWITCH>");
            fprintf(logout,"Line no %d: TOKEN <SWITCH> Lexeme %s found\n",line_count,yytext);
        }
        "case"    {
            fprintf(tokenout,"<CASE>");
            fprintf(logout,"Line no %d: TOKEN <CASE> Lexeme %s found\n",line_count,yytext);
        }
        "default"    {
            fprintf(tokenout,"<DEFAULT>");
            fprintf(logout,"Line no %d: TOKEN <DEFAULT> Lexeme %s found\n",line_count,yytext);
        }
        "continue"    {
            fprintf(tokenout,"<CONTINUE>");
            fprintf(logout,"Line no %d: TOKEN <CONTINUE> Lexeme %s found\n",line_count,yytext);
        }

        "+"|"-"        {
            fprintf(tokenout,"<ADDOP,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <ADDOP> Lexeme %s found\n",line_count,yytext);
            
            //insert in symbol table and print symbol table content(only non empty buckets)
            // There is a '|' in "+"'s rule, this means match execute the action for following rule
        }
        
        "*"|"/"|"%"    {
            fprintf(tokenout,"<MULOP,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <MULOP> Lexeme %s found\n",line_count,yytext);
           
                }
                
        "++"|"--"    {
            fprintf(tokenout,"<INOP,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <INOP> Lexeme %s found\n",line_count,yytext);
           
                }
        "<"|"<="|">"|">="|"=="|"!="   {
        fprintf(tokenout,"<RELOP,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <RELOP> Lexeme %s found\n",line_count,yytext);
            table.Insert("RELOP",yytext);
        
                
        }
        "="            {
        fprintf(tokenout,"<ASSIGNOP,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <ASSIGNOP> Lexeme %s found\n",line_count,yytext);
        
        
        }
        "&&"|"||"        {
        fprintf(tokenout,"<LOGICOP,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <LOGICOP> Lexeme %s found\n",line_count,yytext);
           
        
        }
        "&"|"|"|"^"|"<<"|">>"    {
        fprintf(tokenout,"<BITOP,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <BITOP> Lexeme %s found\n",line_count,yytext);
         
        }
        "!"        {fprintf(tokenout,"<NOT,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <NOT> Lexeme %s found\n",line_count,yytext);
         
        }
        "("        {fprintf(tokenout,"<LPAREN,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <LPAREN> Lexeme %s found\n",line_count,yytext);
           
        }
        ")"        {fprintf(tokenout,"<RPAREN,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <RPAREN> Lexeme %s found\n",line_count,yytext);
            
        }
        "{"        {fprintf(tokenout,"<LCURL,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <LCURL> Lexeme %s found\n",line_count,yytext);
         
         
        }
        "}"        {fprintf(tokenout,"<RCURL,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <RCURL> Lexeme %s found\n",line_count,yytext);
           
        }
        "["        {fprintf(tokenout,"<LTHIRD,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <LTHIRD> Lexeme %s found\n",line_count,yytext);
            
        }
        "]"        {
        fprintf(tokenout,"<RTHIRD,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <RTHIRD> Lexeme %s found\n",line_count,yytext);
            
        }
        ","        {
        fprintf(tokenout,"<COMMA,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <COMMA> Lexeme %s found\n",line_count,yytext);
       
        }
        ";"        {
        fprintf(tokenout,"<SEMICOLON,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <COMMA> Lexeme %s found\n",line_count,yytext);
        }
            
            
            [0-9]+    {
                fprintf(tokenout,"<CONST_INT,%s>",yytext);
                fprintf(logout,"Line no %d: TOKEN <CONST_INT> Lexeme %s found\n",line_count,yytext);
                table.Insert("CONST_INT",yytext);
                table.PrintCurrentScopeTable();
                //insert in symbol table and print symbol table content(only non empty buckets)
            }
            {CONSTFLOAT} {
        
        fprintf(tokenout,"<CONST_FLOAT,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <CONST_FLOAT> Lexeme %s found\n",line_count,yytext);
        
        table.Insert("CONST_FLOAT",yytext);
                table.PrintCurrentScopeTable();
        }
        
        {CONSTCHAR}    {
        
        int i;
        yyleng--;
        char *yycopy = strdup( yytext );
        char separatedChar[3];
        int backslash = 0;
         //printf("in const characters are parsed: ");
        for ( i = 1; i <yyleng;i++ ) {
        if(yycopy[i]=='\\'&&yycopy[i-1]!='\\') {backslash=1;continue;}
        if(backslash ==0)  {
        //printf("%c ",yycopy[i]);
        char c = yycopy[i];
        char str1[2] = {c , '\0'};
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,str1);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        
        }
        else 
        {
        char c;
        if(yycopy[i]=='n') {
	
        c = '\n';
        //printf("%c ",c);
	char separated[3] = {'\\','n','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
        else if(yycopy[i]=='t') {
        c = '\t';
        //printf("%c ",c);
char separated[3] = {'\\','t','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
        else if(yycopy[i]=='a') {
        c = '\a';
        //printf("%c ",c);
char separated[3] = {'\\','a','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
        else if(yycopy[i]=='f') {
        c = '\f';
        //printf("%c ",c);
char separated[3] = {'\\','f','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
        else if(yycopy[i]=='r') {
        c = '\r';
        //printf("%c ",c);
char separated[3] = {'\\','r','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
        else if(yycopy[i]=='b') {
        c = '\b';
        //printf("%c ",c);
char separated[3] = {'\\','b','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
        else if(yycopy[i]=='v') {
        c = '\v';
        //printf("%c ",c);
char separated[3] = {'\\','v','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
        else if(yycopy[i]=='0') {
        c = '\0';
        //printf("%c ",c);
char separated[3] = {'\\','0','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
        else if(yycopy[i]=='\\') {
        c = '\\';
        //printf("%c ",c);
char separated[3] = {'\\','\\','\0'};
        char str1[2] = {c , '\0'};
        
        fprintf(tokenout,"<CONST_CHAR,%s>",str1);
        fprintf(logout,"Line no %d: TOKEN <CONST_CHAR> Lexeme %s found\n",line_count,separated);
        table.Insert("CONST_CHAR",str1);
        table.PrintCurrentScopeTable();
        }
   
        
        backslash=0;
        }
        }
        
        
    //printf("parsing is done");    
    free( yycopy );
            }
            
            
        {STRING}    {
        stringLineNo = line_count;
        //printf("\n(%s single line e captured hoise)\n",yytext);
        StringParsing();
         
        } 
        
        
        
        
        {ID}  {
        fprintf(tokenout,"<ID,%s>",yytext);
            fprintf(logout,"Line no %d: TOKEN <ID> Lexeme %s found\n",line_count,yytext);
            table.Insert("ID",yytext);
            table.PrintCurrentScopeTable();
        
        }
        
        
       

         


        "/*"         {
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
//cout << commentnew;
++line_count;
string temp(yytext);
	commentnew=commentnew+temp;
//cout << commentnew;
}

<comment>"*"+"/"       {
string temp(yytext);
	commentnew=commentnew+temp;
	//cout << commentnew;
len = commentnew.size();
  char *str=new char[len+1];
std::copy(commentnew.begin(),commentnew.end(),str);
str[len]='\0';
//cout << "final comment:   " << commentnew;


fprintf(logout,"Line no %d: TOKEN <COMMENT> Lexeme %s found\n",commentLineNo,str);

 BEGIN(INITIAL);
 }




        "//"         {
        commentLineNo = line_count;
        //printf("\n COMMENT started at %s\n",yytext);
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
fprintf(logout,"Line no %d: TOKEN <COMMENT> Lexeme %s found\n",commentLineNo,str);

commentnew.clear();
BEGIN(INITIAL);
}
        
        
        {INVALIDID} {
        IncEc();
        fprintf(logout,"Error at Line no %d: INVALID IDENTIFIER found %s\n",line_count,yytext);
        ////printf("\nINVALID IDENTIFIER FOUND\n");
        }
        {ILLFORMEDNUMBER} {
        IncEc();
        fprintf(logout,"Error at Line no %d: ILLFORMED NUMBER found %s\n",line_count,yytext);
        ////printf("\nILLFORMED NUMBER FOUND\n");
        }
        {TOOMANYDECIMALPOINTS} {
        IncEc();\
        fprintf(logout,"Error at Line no %d: TOO MANY DECIMAL POINTS found %s\n",line_count,yytext);
        ////printf("\nTOO MANY DECIMAL POINTS FOUND\n");
        }
        {MULTICHAR} {
        IncEc();
        fprintf(logout,"Error at Line no %d: MULTICHARACTER CONSTANT ERROR found %s\n",line_count,yytext);
        ////printf("\nMULTICHARACTER CONSTANT ERROR FOUND\n");
        }
        {EMPTYCHAR} {
        IncEc();
        fprintf(logout,"Error at Line no %d: EMPTY CHARACTER found %s\n",line_count,yytext);
        ////printf("\nEMPTY CHARACTER FOUND\n");
        }
        
        {UNFINISHEDCHAR} {
        IncEc();
        fprintf(logout,"Error at Line no %d: UNFINISHED CHARACTER found %s\n",line_count,yytext);
        ////printf("\nUNFINISHED CHARACTER FOUND\n");
        }
        {UNFINISHEDSTRING} {
        IncEc();

        fprintf(logout,"Error at Line no %d: UNFINISHED STRING found %s\n",line_count,yytext);
	UnStringParsing();
        //printf("\nNEW UNFINISHED STRING FOUND %s\n",yytext);
        }
 	{UNRECOGNIZEDCHAR} {
        IncEc();

        fprintf(logout,"Error at Line no %d: UNRECOGNIZED CHARACTER found %s\n",line_count,yytext);
 
        }
        
        
                 
        
        
        <comment><<EOF>> {
			line_count--;
       		        IncEc();
                        len = commentnew.size();
      		        char *str=new char[len+1];
			std::copy(commentnew.begin(),commentnew.end(),str);
			str[len]='\0';
			//cout << "unfinished final comment:   " << commentnew;
                      
                        fprintf(logout,"Error at Line no %d: UNFINISHED COMMENT found %s\n",commentLineNo,str);
			
                        fprintf(logout,"Total Line Number: %d and error : %d\n",line_count,error_count); 
                        yyterminate();
                        //printf("Total Line Number: %d and error : %d\n",line_count,error_count); 
                        return 0;
                        }
                    
                        <<EOF>> {
			line_count--;
                        //printf("Total Line Number: %d and error: %d\n",line_count,error_count); 
                        fprintf(logout,"Total Line Number: %d and error : %d\n",line_count,error_count); 
                        return 0;
                        }
        
    
        
        
            
        

            

%%

int main(int argc,char *argv[]){
    
    if(argc!=2){
        //printf("Please provide input file name and try again\n");
        return 0;
    }
    
    FILE *fin=fopen(argv[1],"r");
    if(fin==NULL){
        //printf("Cannot open specified file\n");
        return 0;
    }
    
    logout= fopen("log.txt","w");
    tokenout= fopen("token.txt","w");

    yyin= fin;
    yylex();
    fclose(yyin);
    //printf("from main: %d \n",line_count);
    fclose(tokenout);
    fclose(logout);
    return 0;
}




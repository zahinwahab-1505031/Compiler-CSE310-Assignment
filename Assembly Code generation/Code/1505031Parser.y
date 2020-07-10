%{
#include<iostream>
#include<fstream>
#include<cstdlib>
#include<cstring>
#include<cmath>
#include<cstdio>
#include<stdlib.h>
#include<fstream>
#include<set>
#include<iterator>
#include<vector>
#include<algorithm>
#include<istream>
#include<sstream>
#include<queue>
#include "1505031_SymbolTable.h"
#define YYSTYPE SymbolInfo*

using namespace std;

int yyparse(void);
int yylex(void);
extern FILE *yyin;
//extern void eat_to_newline(void);
FILE *fp;
FILE *fp2;
FILE *fp3;
ofstream logout;
ofstream errout;
ofstream debugout;
ofstream debugfile;
ofstream codedebug;
SymbolTable table(50) ;
int line_count=1;
int semantic_errors = 0;
int lexical_errors = 0;
int syntactic_errors = 0;
int lineOfVoid = -99999;
int returnStatementFound = -99999;
string compound_statementStr;
string typeSpec;
string retType;

int labelCount=0;
int tempCount=0;

bool isVoidFunctionCalled = false;
vector <SymbolInfo>parameterList;
vector <string>argumentsPassed;
vector <SymbolInfo>parametersPassed;
vector <string>variableList;
vector <string>arrayList;
vector <string>varInFuncList;
vector <SymbolInfo>dataList;
vector <int>arraySizeList;
int argumentsCount = 0;
string currentFunction;
void yyerror(char *s)
{
	syntactic_errors++;
	logout <<  endl; 
        logout << "at line no: " << line_count << "  "<< s <<endl;
	errout<< endl; errout << endl;
	errout<< endl; errout << "Error at line no: " << line_count <<"  "<< s <<endl;
	//fprintf(stderr,"%s\n",s);
	return;
}


char *newLabel()
{
	char *lb= new char[4];
	strcpy(lb,"L");
	char b[3];
	sprintf(b,"%d", labelCount);
	labelCount++;
	strcat(lb,b);
	return lb;
}

char *newTemp()
{
	char *t= new char[4];
	strcpy(t,"t");
	char b[3];
	sprintf(b,"%d", tempCount);
	tempCount++;
	strcat(t,b);
	return t;
}

string PrintFunction(){


	return "\n\nDECIMAL_OUT PROC NEAR\n\npush ax\npush bx\npush cx\npush dx\nor ax,ax\njge enddif\npush ax\nmov dl,'-'\nmov ah,2\nint 21h\npop ax\nneg ax\nenddif:\nxor cx,cx\nmov bx,10d\nrepeat:\nxor dx,dx\ndiv bx\npush dx\ninc cx\nor ax,ax\njne repeat\nmov ah,2\nprint_loop:\npop dx\nor dl,30h\nint 21h\nloop print_loop\npop dx\npop cx\npop bx\npop ax\nret\n\nDECIMAL_OUT ENDP\n";
			
}
string makeString(int id){
	ostringstream oss;
	oss << id;
	return oss.str();
}
				
SymbolInfo *makePointer(SymbolInfo ob,int id) {
	


SymbolInfo *s = new SymbolInfo();
			       s->setSymbolName(ob.getSymbolName());
s->setSymbolType(ob.getSymbolType());
s->next = NULL;
s->setIdentifierType(ob.getIdentifierType()); //FUNC,ARRAY,VAR

s->match = ob.match;
s->code  = ob.code;
s->assemblyName  = "[bp+"+makeString(id)+"]";
    s->parameters = ob.parameters;
    s->varInfo = ob.varInfo;
    s->funcInfo = ob.funcInfo;
s->arrInfo = ob.arrInfo;
return s;
}
%}

%token IF ELSE FOR WHILE DO BREAK INT CHAR FLOAT DOUBLE VOID RETURN SWITCH CASE DEFAULT CONTINUE ADDOP MULOP INCOP DECOP RELOP ASSIGNOP LOGICOP BITOP NOT LPAREN RPAREN LTHIRD RTHIRD LCURL RCURL COMMA SEMICOLON CONST_INT CONST_FLOAT CONST_CHAR ID PRINTLN 

//%left 
//%right
%error-verbose
%nonassoc LOWER_THAN_ELSE
%nonassoc ELSE


%%

start : program
	{
		

		logout <<  endl; logout << "at line no: "<< line_count << " start : program\n";

		logout<< $1->match<<endl;
		debugout << ".model small\n";
		debugout << ".stack 100h\n";
		debugout << "\n.data\n" ;
		for(int i=0;i<tempCount;i++){
			ostringstream oss;
			oss<< i;
			string name = "t"+oss.str();
			 debugout << name << " dw ?\n";
	
		}
		for(int i=0;i<variableList.size();i++){
 				debugout <<variableList[i] << " dw ?\n";
			 	}
		for(int i=0;i<arrayList.size();i++){
			debugout << arrayList[i] <<" dw "<< arraySizeList[i]<< " dup(0)\n";
		}
		
		debugout << "\n.code \n"; 
		debugout << PrintFunction();
		debugout << $1->code;
		debugout << "end main\n";
           
	}
	;

program : program unit      
	{
        logout <<  endl; logout << "at line no: "<< line_count << " program : program unit\n";
		
		$$ = new SymbolInfo($1); 
		$$->match = $1->match+ "\n" +$2->match;
		$$->code = $1->code+ "\n" +$2->code;
		logout <<  endl; logout << $1->match<<endl;
	}
	| unit             
 	{
		logout <<  endl; logout << "at line no: "<< line_count << " program : unit\n";
		$$ = new SymbolInfo($1); 
		logout<< $1->match<<endl;
	}
	;
	
unit :  var_declaration      
	{
		$$ = new SymbolInfo($1); 
		logout <<  endl; logout << "at line no: "<< line_count <<" unit : var_declaration\n";
		logout <<  endl; logout << $$->match << endl;
	} 
     |  func_declaration		
	{
		$$ = new SymbolInfo($1); 
		logout <<  endl; logout << "at line no: "<< line_count <<" unit : func_declaration\n";
		logout <<  endl; logout << $$->match << endl;
	}
     |  func_definition		
	{
		$$ = new SymbolInfo($1); 
		logout <<  endl; logout << "at line no: "<< line_count <<" unit : func_definition\n";
		logout <<  endl; logout << $$->match << endl;
	} 
     ;
     
func_declaration : type_specifier ID LPAREN parameter_list RPAREN SEMICOLON 
	{
		
		SymbolInfo *s = table.LookUp ($2->getSymbolName());
		if(s==NULL) {

			 table.Insert($2->getSymbolName(),"ID");
			 s = table.LookUp ($2->getSymbolName());
			 s->setIdentifierType("FUNCTION");
			 s->parameters = parameterList;

			 parameterList.clear();
			 s->funcInfo.returnType = $1->getSymbolType();
		}
		else {
			parameterList.clear();
			semantic_errors++; errout<< endl; errout<< "Error at line no: "<< line_count << " function "<< $2->getSymbolName() << " already declared" <<endl; }
			s->match = $1->match + $2->getSymbolName() + "(" + $4->match + ")" + ";";
			$$ = new SymbolInfo(s);
			logout <<  endl; logout << "at line no: "<< line_count <<" func_declaration : type_specifier ID LPAREN parameter_list RPAREN SEMICOLON \n";
			logout <<  endl; logout << s->match << endl;

	}
		| type_specifier ID LPAREN RPAREN SEMICOLON
	{
		
		SymbolInfo *s = table.LookUp ($2->getSymbolName());
		if(s==NULL) {
			 table.Insert($2->getSymbolName(),"ID");
			 s = table.LookUp ($2->getSymbolName());
			 s->setIdentifierType("FUNCTION"); 
			 s->funcInfo.returnType = $1->getSymbolType();
		}
		else {semantic_errors++; errout<< endl; errout<< "Error at line no: "<< line_count << " function "<< $2->getSymbolName() << " already declared" <<endl;}
		s->match = $1->match + $2->getSymbolName() + "(" + ")" + ";";
		$$ = new SymbolInfo(s);
		logout <<  endl; logout << "at line no: "<< line_count <<" func_declaration : type_specifier ID LPAREN RPAREN SEMICOLON \n";
		logout <<  endl; logout << s->match << endl;

	}
	| type_specifier ID LPAREN parameter_list RPAREN error
	{
		
		SymbolInfo *s = table.LookUp ($2->getSymbolName());
		if(s==NULL) {
			 table.Insert($2->getSymbolName(),"ID");
			 s = table.LookUp ($2->getSymbolName());
			 s->setIdentifierType("FUNCTION");
 			 s->parameters = parameterList;
			 parameterList.clear();
			 s->funcInfo.returnType = $1->getSymbolType();
		}
		else {parameterList.clear();semantic_errors++; errout<< endl; errout<< "Error at line no: "<< line_count << " function "<< $2->getSymbolName() << " already declared" <<endl;}
		s->match = $1->match + $2->getSymbolName() + "(" + $4->match+ ")" ;
		$$ = new SymbolInfo(s);
		logout <<  endl; logout << "at line no: "<< line_count <<" func_declaration : type_specifier ID LPAREN parameter_list RPAREN error \n";
		//errout<< endl; errout << "at line no: "<< line_count <<" Semicolon missing";
		logout <<  endl; logout << s->match << endl;

	} 
	| type_specifier ID LPAREN RPAREN error
	{
		
		SymbolInfo *s = table.LookUp ($2->getSymbolName());
		if(s==NULL) {
			 table.Insert($2->getSymbolName(),"ID");
			 s = table.LookUp ($2->getSymbolName());
			 s->setIdentifierType("FUNCTION");
			 s->funcInfo.returnType = $1->getSymbolType();
		}
		else {semantic_errors++; errout<< endl; errout<< "Error at line no: "<< line_count << " function "<< $2->getSymbolName() << " already declared" <<endl;}
		s->match = $1->match + $2->getSymbolName() + "(" + ")";
		$$ = new SymbolInfo(s);
		logout <<  endl; logout << "at line no: "<< line_count <<" func_declaration : type_specifier ID LPAREN RPAREN error \n";
		{//syntactic_errors++; errout<< endl; errout << "at line no: "<< line_count <<" Semicolon missing";
		}
		logout <<  endl; logout << s->match << endl;

	} 
	
		;
		 
func_definition : type_specifier ID LPAREN parameter_list RPAREN 
		{
			currentFunction = $2->getSymbolName();
		SymbolInfo *s = table.currentScope->LookUp($2->getSymbolName());
		if(s==NULL){
		 table.Insert($2->getSymbolName(),"ID");
			 s = table.LookUp ($2->getSymbolName());
			 s->setIdentifierType("FUNCTION");
			 s->funcInfo.returnType = $1->getSymbolType();
			 s->parameters = parameterList;
			s->funcInfo.isAlreadyDefined = true;

		}
		else if(s->getIdentifierType()=="FUNCTION") {
if(s->funcInfo.isAlreadyDefined == true) {semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<line_count << " function " << $2->getSymbolName() << " is already defined \n";}
else if(s->funcInfo.isAlreadyDefined == false) {s->funcInfo.isAlreadyDefined = true;}
		if( s->funcInfo.returnType != $1->getSymbolType()) {
		semantic_errors++;errout<< endl; errout<< "Error at line no: "<< line_count <<" return type does not match the declaration \n";}
		
		if(s->parameters.size()!=parameterList.size()){
retType.clear();semantic_errors++; errout<< endl; errout<< "Error at line no: "<< line_count <<" no of parameters mismatch \n";

		
		}
		if(s->parameters.size()==parameterList.size()){
		for(int i=0;i<parameterList.size();i++) {
			if(s->parameters[i].varInfo.variableType != parameterList[i].varInfo.variableType) 
			{
semantic_errors++; errout<< endl; errout<< "Error at line no: "<< line_count <<" type of parameters mismatch \n";}
		}
		
		}
		//semantic errors handle korte hobe
		} 
} compound_statement {
SymbolInfo *s = table.currentScope->LookUp($2->getSymbolName());
int len = retType.length();
	
   if(s->funcInfo.returnType== "INT"&& retType=="FLOAT") 
	{retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<returnStatementFound << " return type mismatch \n";}
	  else if (s->funcInfo.returnType== "FLOAT"&& retType=="INT") 	  
	 {retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<returnStatementFound << " return type mismatch \n";}
	   else if (s->funcInfo.returnType== "VOID"&& retType=="INT") 	  
	 {retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<returnStatementFound << " VOID return type should not return anything \n";}
	   else if (s->funcInfo.returnType== "VOID"&& retType=="FLOAT") 	  
	 {retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<returnStatementFound << " VOID return type should not return anything \n";}
 else if(s->funcInfo.returnType== "INT" && len==0) 
	{retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<line_count << " Integer return type must return anything \n";}
	  else if (s->funcInfo.returnType== "FLOAT"&& len == 0) 	  
	 {retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<line_count << " Float return type must return anything \n";}
parameterList.clear();
retType.clear();
		s->match = $1->match + $2->getSymbolName() + "(" + $4->match + ")" + $7->match;
compound_statementStr.clear();
		$$=new SymbolInfo();
		$$->code = $2->getSymbolName()+ " PROC\n";
		if($2->getSymbolName()=="main") {

			$$->code+="\nmov ax,@data\nmov ds,ax\n";
		}
		else if($2->getSymbolName()!="main") {

			$$->code += "push bp\n";
			$$->code += "mov bp,sp\n";
			int j=4;
			for(int i=0;i<varInFuncList.size();i++) {
				ostringstream oss;
				oss << j;

				$$->code += "mov ax,bp["+oss.str()+"]\n";
					$$->code += "mov "+ varInFuncList[i]+",ax\n";
				j+=2;
			}
			varInFuncList.clear();
		}
		$$->code+="\n"+$7->code;
		if($2->getSymbolName()=="main") {

			$$->code+="mov ah,4ch\nint 21h\n";
			$$->code+="main endp\n";
		}
		else {
		 if(s->funcInfo.returnType!="VOID"){
			
			$$->code+=$2->getSymbolName()+" endp\n";
		}
			else if(s->funcInfo.returnType=="VOID"){
			$$->code += "pop bp\n";
		
			$$->code+="ret\n";
			$$->code+=$2->getSymbolName()+" endp\n";
		}
	}

		






		logout <<  endl; logout << "at line no: "<< line_count << "func_definition : type_specifier ID LPAREN parameter_list RPAREN compound_statement\n";
		logout <<  endl; logout << s->match <<endl;
		}
		| type_specifier ID LPAREN RPAREN 
		{
				currentFunction = $2->getSymbolName();
		SymbolInfo *s = table.LookUp($2->getSymbolName());
		if(s==NULL){
		 table.Insert($2->getSymbolName(),"ID");
			 s = table.LookUp ($2->getSymbolName());
			 s->setIdentifierType("FUNCTION");
			 s->funcInfo.returnType = $1->getSymbolType();
			 s->funcInfo.isAlreadyDefined = true;
	  		
		} 		
else if(s->getIdentifierType()=="FUNCTION") {
		if(s->funcInfo.isAlreadyDefined == true) {semantic_errors++;  errout<< endl; errout<< "Error at line no: " 			<<line_count << " function " << $2->getSymbolName() << " is already defined \n";}
		else if(s->funcInfo.isAlreadyDefined == false) {s->funcInfo.isAlreadyDefined = true;}
		
		if($1->getSymbolType()!=s->funcInfo.returnType) {semantic_errors++;errout<< endl; errout<< "Error at line no: " <<line_count << " return type does not match the declaration \n";}
			
	
		//semantic errors handle korte hobe
		} } compound_statement {
SymbolInfo *s = table.LookUp($2->getSymbolName());		 if(s->getIdentifierType()=="FUNCTION") {
		int len = retType.length();
	
   if(s->funcInfo.returnType== "INT"&& retType=="FLOAT") 
	{retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<returnStatementFound << " return type mismatch \n";}
	  else if (s->funcInfo.returnType== "FLOAT"&& retType=="INT") 	  
	 {retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<returnStatementFound << " return type mismatch \n";}
	   else if (s->funcInfo.returnType== "VOID"&& retType=="INT") 	  
	 {retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<returnStatementFound << " VOID return type should not return anything \n";}
	   else if (s->funcInfo.returnType== "VOID"&& retType=="FLOAT") 	  
	 {retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<returnStatementFound << " VOID return type should not return anything \n";}
	  else if(s->funcInfo.returnType== "INT" && len==0) 
	{retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<line_count << " Integer return type must return anything \n";}
	  else if (s->funcInfo.returnType== "FLOAT"&& len == 0) 	  
	 {retType.clear();semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<line_count << " Float return type must return anything \n";}
parameterList.clear();
retType.clear();
		}
		else if(s->getIdentifierType()!="FUNCTION") 
		{semantic_errors++; errout<< endl; errout<< "Error at line no: "<< line_count <<" identifier "<<$2->getSymbolName()<<" is not declared as function \n";}
		
		logout <<  endl; logout << "at line no: "<< line_count << " func_definition : type_specifier ID LPAREN RPAREN compound_statement\n";
retType.clear();
		s->match = $1->match + $2->getSymbolName() + "(" + ")" +$6->match;
		$$=s;
		$$=new SymbolInfo();
		$$->code = $2->getSymbolName()+ " PROC\n";
		if($2->getSymbolName()=="main") {

			$$->code+="mov ax,@data\nmov ds,ax\n";
		}
		$$->code+=$6->code;
	if($2->getSymbolName()=="main") {

			$$->code+="mov ah,4ch\nint 21h\n";
			$$->code+="main endp\n";
		}
		else {
		 if(s->funcInfo.returnType!="VOID"){
			
			$$->code+=$2->getSymbolName()+" endp\n";
		}
			else if(s->funcInfo.returnType=="VOID"){
			
			$$->code+="ret\n";
			$$->code+=$2->getSymbolName()+" endp\n";
		}
	}

		logout <<  endl; logout << s->match <<endl;
		
		}
 		;				


parameter_list  : parameter_list COMMA type_specifier ID
		{
		//argumentsPassed.push_back(typeSpec);
		SymbolInfo *s = new SymbolInfo($4);
	s->setIdentifierType("VARIABLE");
		s->varInfo.variableType = typeSpec;


		parameterList.push_back(*s);
		s->match = $1->match + "," + $3->match + $4->getSymbolName();
		$$=s;
		logout <<  endl; logout << "at line no: "<< line_count << " parameter_list  : parameter_list COMMA type_specifier ID\n";
		logout <<  endl; logout << s->match <<endl;
		}
		| parameter_list COMMA type_specifier
		{
		SymbolInfo *s = new SymbolInfo($3->getSymbolName(),$3->getSymbolType());
		s->match = $1->match + "," + $3->match;
		$$=s;
		//argumentsPassed.push_back($3->getSymbolType());
		
		logout <<  endl; logout << "at line no: "<< line_count << "parameter_list  : parameter_list COMMA type_specifier ID\n";
		logout <<  endl; logout << s->match <<endl;
		}
 		| type_specifier ID
 		{
 		//argumentsPassed.push_back(typeSpec);
		
		SymbolInfo *s = new SymbolInfo($2);
		s->setIdentifierType("VARIABLE");
		s->varInfo.variableType = typeSpec;
		parameterList.push_back(*s);
		s->match = $1->match+ " " + $2->getSymbolName();
 		$$=s;
		logout <<  endl; logout << "at line no: "<< line_count << "parameter_list  : type_specifier ID\n";
		logout <<  endl; logout << s->match <<endl;
 		
 		}
		| type_specifier 
		{
		//argumentsPassed.push_back($1->getSymbolType());
		SymbolInfo *s = new SymbolInfo($1->getSymbolName(),$1->getSymbolType());
		
		s->match = $1->match;
		$$=s;
		logout <<  endl; logout << "at line no: "<< line_count << "parameter_list  : type_specifier\n";
		logout <<  endl; logout << s->match <<endl;
		}
 		;

	
compound_statement : LCURL {
		debugfile << "\n\n---------before entering new scope----------------\n";
		debugfile << table.PrintAllScopeTable();
		debugfile << "\n---------done printing----------------\n\n";
		logout <<  endl; debugfile << table.EnterScope(); 
		int p = 4;
		for(int i = 0; i<parameterList.size(); i++) {
		//	cout << parameterList[i].getSymbolName() << " " << parameterList[i].getSymbolType() <<endl;
		SymbolInfo *s = makePointer(parameterList[i],p);
		p+=2 ;
		
	 debugfile << "printing symbol before pushing into symbol table\n";
		debugfile << s->printSymbol()<<endl;
		table.Insert(s);
		string str = s->getSymbolName()+makeString(table.currentScope->id);
		variableList.push_back(str);
	varInFuncList.push_back(str);
		dataList.push_back(s);
		}
		debugfile << "\n\n---------after pushing into table----------------\n";
		debugfile << table.PrintAllScopeTable();
		debugfile << "\n--------done printing----------------\n";
		//
		} statements {
		//logout <<  endl; logout << "----------------" << $$->match <<"--------------\n";
		
		} RCURL {
		
		}
		{
		SymbolInfo *s = new SymbolInfo("$","$");
 		    s->match = "{\n"  +  $3->match + "\n}";
compound_statementStr = s->match;
		    $$ = new SymbolInfo(s);
		    $$->code = $3->code;
		    logout <<  endl; logout << "at line no: "<< line_count <<"compound_statement : LCURL statements RCURL\n";
		logout <<  endl; logout << $$->match <<endl;
logout <<  endl; debugfile << table.PrintAllScopeTable();
		logout <<  endl; debugfile << table.ExitScope();

		
		
		}
 		    | LCURL {
		logout <<  endl; logout << table.EnterScope(); 
		int p=4;
		for(int i = 0; i<parameterList.size(); i++) {
		                
		//	cout << parameterList[i].getSymbolName() << " " << parameterList[i].getSymbolType() <<endl;
		SymbolInfo *s = makePointer(parameterList[i],p);
		p+=2 ;
		
	 debugfile << "printing symbol before pushing into symbol table\n";
		debugfile << s->printSymbol()<<endl;
		table.Insert(s);
		string str = s->getSymbolName()+makeString(table.currentScope->id);
		variableList.push_back(str);
	varInFuncList.push_back(str);
		dataList.push_back(s);

		}
		
		} RCURL {logout <<  endl; logout << table.PrintAllScopeTable();logout <<  endl; logout << table.ExitScope();}
 		    {
 		    SymbolInfo *s = new SymbolInfo("$","$");
 		    s->match = "{ }";
				compound_statementStr = s->match;
		    $$ = new SymbolInfo(s);
		    $$->code = "";
		    logout <<  endl; logout << "at line no: "<< line_count <<"compound_statement : LCURL RCURL\n";
		    logout <<  endl; logout << $$->match <<endl;
 		    }
 		    ;
 		    
var_declaration : type_specifier declaration_list SEMICOLON
{ 
logout <<  endl; 
$1->match= $1->match + $2->match+";";
$$ = new SymbolInfo($1); 
logout <<  endl; logout << "at line no: "<< line_count <<" var_declaration : type_specifier declaration_list SEMICOLON\n";
logout <<  endl; logout << $1->match <<endl;
}
|type_specifier declaration_list error
{ 
logout <<  endl; 
$1->match= $1->match + $2->match;
$$ = new SymbolInfo($1); 
logout <<  endl; logout << "at line no: "<< line_count <<" var_declaration : type_specifier declaration_list error\n";
//syntactic_errors++;
//errout<< endl; errout << "at line no: "<< line_count << " semicolon missing \n";
logout <<  endl; logout << $1->match <<endl;
}
 		 ;
 		 
type_specifier	: INT    
{
		 SymbolInfo *s = new SymbolInfo("int","INT");
		 s->match = "int ";
		 $$=s;  
		 typeSpec = "INT";
		 logout <<  endl; logout << "at line no: "<< line_count <<" type_specifier : INT\n";
                 logout <<  endl; logout << $$->match <<endl;
	
}
 		| FLOAT 
{ 
		SymbolInfo *s = new SymbolInfo("float","FLOAT");
		s->match = "float ";
		$$=s; 
		typeSpec = "FLOAT";
		logout<< "at line no:" <<line_count << " type_specifier : FLOAT\n";
		logout <<  endl; logout << $$->match <<endl;
}
 		| VOID   
{
		SymbolInfo *s = new SymbolInfo("void","VOID"); 
		s->match = "void ";
		$$=s;
		typeSpec = "VOID";
		logout<< "at line no:" <<line_count << " type_specifier : VOID\n";
		logout <<  endl; logout << $$->match<<endl;
}
 		;
 		
declaration_list : declaration_list COMMA ID 		
{ 
				SymbolInfo *s = table.currentScope->LookUp($3->getSymbolName());
				if(s==NULL)
				{
								
					table.Insert($3->getSymbolName(),$3->getSymbolType());
					s = table.currentScope->LookUp($3->getSymbolName());

					//s->assemblyName = $3->getSymbolName()
					s->setIdentifierType("VARIABLE");
					s->varInfo.setVariableType(typeSpec);
					ostringstream oss;
					oss<<table.currentScope->id;
					s->setAssemblyName(s->getSymbolName()+oss.str());
					//cout << s->assemblyName;
					dataList.push_back(s);

		variableList.push_back(s->getSymbolName()+oss.str());
					//logout <<  endl; logout << table.PrintCurrentScopeTable();
				}
				else {	semantic_errors++;
errout<< endl; errout<< "Error at line no: " <<line_count << " variable " << $3->getSymbolName() << " already declared\n";
}
				s->match = $1->match + ","+ $3->getSymbolName();
				$$ = new SymbolInfo(s);
				logout<< "at line no:" <<line_count << "  declaration_list : declaration_list COMMA ID\n";
				logout <<  endl; logout << s->match <<endl;
}	                               
 		  | declaration_list COMMA ID LTHIRD CONST_INT RTHIRD		
{ 
				SymbolInfo *s = table.currentScope->LookUp($3->getSymbolName());
				if(s==NULL)
				{
								
					table.Insert($3->getSymbolName(),$3->getSymbolType());
					s = table.currentScope->LookUp($3->getSymbolName());
					s->setIdentifierType("ARRAY");
					int i = atoi($5->getSymbolName().c_str());
					s->arrInfo.setArraySize(i);
					s->arrInfo.setArrayType(typeSpec);
					ostringstream oss;
					oss<<table.currentScope->id;
					s->setAssemblyName(s->getSymbolName()+oss.str());
					//cout << s->assemblyName;
					dataList.push_back(s);
					arrayList.push_back(s->getSymbolName()+oss.str());
					arraySizeList.push_back(i);
					if(typeSpec == "INT"){
					for (int k=0;k<i;k++) s->arrInfo.vector_integers.push_back(0);
					}
					
					else if(typeSpec == "FLOAT"){
					for (int k=0;k<i;k++) s->arrInfo.vector_floats.push_back(0);
					}
				}
				else logout <<  endl; logout << "Already declared"<<endl;
				
			 s->match = $1->match + " , "+ $3->getSymbolName() + "[" + $5->getSymbolName() + "]";
		       
		      
		        $$ = new SymbolInfo(s);
		       logout<< "at line no:" <<line_count << " declaration_list : declaration_list COMMA ID LTHIRD CONST_INT RTHIRD\n";
			logout <<  endl; logout << s->match<<endl;
}	 
 		  | ID	
{
				 
				
				SymbolInfo *s = table.currentScope->LookUp($1->getSymbolName());
				if(s==NULL)
				{
								
					table.Insert($1->getSymbolName(),$1->getSymbolType());
					s = table.currentScope->LookUp($1->getSymbolName());
					s->setIdentifierType("VARIABLE");
					s->varInfo.setVariableType(typeSpec);
					ostringstream oss;
					oss<<table.currentScope->id;
					s->setAssemblyName(s->getSymbolName()+oss.str());
					//cout << s->assemblyName;
					dataList.push_back(s);

		variableList.push_back(s->getSymbolName()+oss.str());
					//logout <<  endl; logout << table.PrintCurrentScopeTable();
				}
				else 
   {semantic_errors++; errout<< endl; errout<< "Error at line no: " <<line_count << " Variable " << $1->getSymbolName() <<" already declared\n";}
				s->match = $1->getSymbolName();
				$$ = new SymbolInfo(s);
				logout<< "at line no:" <<line_count << " declaration_list-> ID\n";
				logout <<  endl; logout << s->match<<endl;
}								
 		  | ID LTHIRD CONST_INT RTHIRD 

{ 
				
				
				SymbolInfo *s = table.currentScope->LookUp($1->getSymbolName());
				if(s==NULL)
				{
								
					table.Insert($1->getSymbolName(),$1->getSymbolType());
					s = table.currentScope->LookUp($1->getSymbolName());
					s->setIdentifierType("ARRAY");
					s->arrInfo.setArrayType(typeSpec);
					int i = atoi($3->getSymbolName().c_str());
					s->arrInfo.setArraySize(i);
					ostringstream oss;
					oss<<table.currentScope->id;
					s->setAssemblyName(s->getSymbolName()+oss.str());
					//cout << s->assemblyName;
					dataList.push_back(s);
					arrayList.push_back(s->getSymbolName()+oss.str());
					arraySizeList.push_back(i);
					if(typeSpec == "INT"){
					for (int k=0;k<i;k++) s->arrInfo.vector_integers.push_back(0);
					}
					
					else if(typeSpec == "FLOAT"){
					for (int k=0;k<i;k++) s->arrInfo.vector_floats.push_back(0);
					}
				}
				else {semantic_errors++; 
				errout<< endl; errout<< "Error at line no: " <<line_count <<"Already declared"<<endl;}
				s->match = $1->getSymbolName()+"["+$3->getSymbolName() +"]";
				$$ = new SymbolInfo(s);
				logout<< "at line no:" <<line_count << " declaration_list :  ID LTHIRD CONST_INT RTHIRD \n";
				logout <<  endl; logout << s->match<<endl;
}      
 		  ;
 		  
statements : statement     		
     	   {
     	   $$=new SymbolInfo($1);
     	   
     	   logout<< "at line no:" <<line_count << " statements : statement\n";
     	  // statementStr = $$->match;
     	   logout <<  endl; logout << $$->match<<endl;
     	   }
	   | statements statement 	
	   {
	   $1->match =  $1->match + "\n" + $2->match;
	   $$ =new SymbolInfo($1);
	   $$->code = $1->code+$2->code;
	   logout<< "at line no:" <<line_count << " statements : statements statement\n";
	 //  statementStr = $$->match;
	   logout <<  endl; logout << $$->match<<endl;
	   }
	   ;
	   
statement : var_declaration     	
	  {
	  $$ = new SymbolInfo($1); 
	  logout<< "at line no:" <<line_count << " statement : var_declaration\n";
	  logout <<  endl; logout << $$->match<<endl;
	  }
	  | expression_statement	
	  {
	  $$ = new SymbolInfo($1); 
	  logout<< "at line no:" <<line_count << " statement : expression_statement\n";
	  logout <<  endl; logout << $$->match<<endl;
	  }
	  | compound_statement		
	  {
	  $$ = new SymbolInfo($1); 
	  logout<< "at line no:" <<line_count << " statement : compound_statement\n";
	  logout <<  endl; logout << $$->match<<endl;
	  }
	  | FOR LPAREN expression_statement expression_statement expression RPAREN statement
	  {
	   $$ = new SymbolInfo(); 
	  string forLabel = string(newLabel());
	  string breaklabel = string(newLabel());
	//  $$->code += ";initializing loop variable\n";

	  $$->code += $3->code;
	  $$->code += "\nmov ax,"+$3->getSymbolName()+"\n";
	//  $$->code += ";for label\n";
	  $$->code += forLabel+":\n";
	  $$->code += $4->code;
	 // $$->code += ";checking for loop condition\n";
	  $$->code += "\nmov ax,"+$4->getSymbolName()+"\n";
	  $$->code += "cmp ax,0\n";
	  $$->code +="je "+breaklabel+"\n";
	 // $$->code += ";statements in for loop\n";
	  $$->code += $7->code;
	 // $$->code += ";incrementing or decrementing loop variable\n";
	  $$->code += $5->code;
	  $$->code += "jmp "+ forLabel+ "\n";
	 // $$->code += ";this is break label\n";
	  $$->code += breaklabel+":\n";
	 /* for (int i=0;i<n;i++) dosth
	   $$ = $3
	   mov ax,$3
	   forLabel:
	   cmp ax,0
	   je breakLabel
	   $7
	   $5
	   jmp forLabel
	   breaklabel



	 */
	  $$->match = "for (" + $3->match + $4->match + $5->match + ")" + $7->match;
	  logout<< "at line no:" <<line_count << " statement : FOR LPAREN expression_statement expression_statement expression RPAREN statement\n";
	  
	   
	  logout <<  endl; logout << $$->match<<endl;
	  }
	  | IF LPAREN expression RPAREN statement %prec LOWER_THAN_ELSE
	  {
	  $1->match = "if ("+$3->match+")" + $5->match;
	  logout<< "at line no:" <<line_count << " statement : IF LPAREN expression RPAREN statement\n";
	 $$ = new SymbolInfo($1); 
	  logout <<  endl; logout << $$->match<<endl;
	  $$->code = $3->code;
	  string doSomething = string(newLabel());
	  string mainCode = string(newLabel());
	  $$->code+="mov ax,"+$3->getSymbolName()+"\n";
	  $$->code+="cmp ax,1\n";
	  $$->code+="je "+doSomething+"\n";
	  $$->code+="jmp "+mainCode+"\n";
	  $$->code+= doSomething+":\n";
	  $$->code+=$5->code;
	  $$->code+=mainCode+":\n";
	//  $$->code += 
	  /*
	  if(a==b) then dosth
	continue with previous job
	mov ax, $2
	cmp ax,1
	je dosth
	jmp continue
	dosth: $5
	continue: */
	  }
	  | IF LPAREN expression RPAREN statement ELSE statement
	  {
	  $1->match = "if ("+$3->match+")" + $5->match + "\n"+ "else" + $7->match;
	  $$ = new SymbolInfo($1);
	  string ifCond = string(newLabel());
	  string elseCond = string(newLabel());
	  string mainCode = string(newLabel());
	  $$->code = $3->code;
	  $$->code+="mov ax,"+$3->getSymbolName()+"\n";
	  $$->code+="cmp ax,1\n";
	  $$->code+="je "+ifCond + "\n";
	  $$->code+="jmp "+elseCond + "\n";
	  $$->code+= ifCond+":\n";
	  $$->code+=$5->code;
	  $$->code+="jmp "+mainCode + "\n";
	  $$->code+= elseCond+":\n";
	  $$->code+=$7->code;
	  $$->code+="jmp "+mainCode+"\n";
	  $$->code+=mainCode+":\n"; 
	   /*
	  if(a==b) then ifstatement code
	  else elsestatement code
	  code:*/
	  logout <<  endl; logout << $$->match<<endl;
	  }
	  | WHILE LPAREN expression RPAREN statement
	  {
	  	/*
	  	while(expression is true) {
		do work
		if expression is false go to exit
	  	exit : }
		while:
		$3->code
	  	mov ax,$3
	  	cmp ax,0
	  	je exit
		$5

	  	exit:
	  	$$ = new SymbolInfo(); 
	  	string whileLabel = string(newLabel());
	  	string breakLabel = string(newLabel());
	  	$$->code += ";whileLabel\n" ;
	  	$$->code = "\t"+whileLabel+":\n";
	  	$$->code += $3->code;
	  	$$->code += ";checking while loop condition\n";
	  	$$->code += "\tmov ax,"+ $3->getSymbolName()+"\n";
	  	$$->code += "\tcmp ax,0 \n";
	  	$$->code += "\tje "+ breakLabel+"\n";
	  	$$->code += "; while loop\n";
	  	$$->code += $5->code;
	  	$$->code += "\tjmp "+ whileLabel+"\n";
	  	$$->code += ";break Label\n" ;
	  	$$->code += "\t"+breakLabel+":\n";

	  	*/
	  	$$ = new SymbolInfo(); 
	  	string whileLabel = string(newLabel());
	  	string breakLabel = string(newLabel());
	  	//$$->code += ";whileLabel\n" ;
	  	$$->code += whileLabel+":\n";
	 //   $$->code += ";working while loop condition\n";
	  	$$->code += $3->code;
	  	//$$->code += ";checking while loop condition\n";
	  	$$->code += "mov ax,"+ $3->getSymbolName()+"\n";
	  	$$->code += "cmp ax,0 \n";
	  	$$->code += "je "+ breakLabel+"\n";
	  	//$$->code += "; while loop\n";
	  	$$->code += $5->code;

	  	$$->code += "jmp "+ whileLabel+"\n";
	  	//$$->code += ";break Label\n" ;
	  	$$->code += breakLabel+":\n";
	    $$->match = "while (" + $3->match + ")" + "\n"+ $5->match;
	    logout<< "at line no:" <<line_count << " statement : WHILE LPAREN expression RPAREN statement\n";
	  
	  logout <<  endl; logout << $$->match<<endl;
	  }
	  | PRINTLN LPAREN ID RPAREN SEMICOLON
	  {
	  
	  logout<< "at line no:" <<line_count << " statement : PRINTLN LPAREN ID RPAREN SEMICOLON\n";
	   $$ = new SymbolInfo(); 
	  $$->match = "println (" + $3->getSymbolName() + ");";
	  logout <<  endl; logout << $$->match<<endl;
	  $$->code = $3->code;
	  $$->code += "mov ax," + $3->getAssemblyName() +"\n";
	  $$->code += "call DECIMAL_OUT\n";
	  $$->code += "mov ah,2\n";
	  $$->code += "mov dl,0dh\n";
	  $$->code += "int 21h\n";
	  $$->code += "mov dl,0ah\n";
	  $$->code += "int 21h\n";
	  }
	  | PRINTLN LPAREN ID RPAREN error
	  {
	  $1->match = "println (" + $3->getSymbolName() + ")";
	  logout<< "at line no:" <<line_count << " statement : PRINTLN LPAREN ID RPAREN error\n";
	  $$ = new SymbolInfo($1); 
	  logout <<  endl; logout << $$->match<<endl;
	  }
	  | RETURN expression SEMICOLON
	  {
	  if($2->getIdentifierType()=="VARIABLE" && $2->varInfo.variableType == "INT") {

	 retType="INT";
}
	  else if ($2->getIdentifierType()=="VARIABLE" && $2->varInfo.variableType == "FLOAT") {
		   retType = "FLOAT"; 
}
else  if($2->getIdentifierType()=="FUNCTION" && $2->funcInfo.returnType == "INT") {

	 retType="INT";
}
	  else if ($2->getIdentifierType()=="FUNCTION" && $2->funcInfo.returnType == "FLOAT") {
		   retType = "FLOAT"; 
}
else  if($2->getIdentifierType()=="ARRAY" && $2->arrInfo.arrayType == "INT") {

	 retType="INT";
}
	  else if ($2->getIdentifierType()=="ARRAY" && $2->arrInfo.arrayType == "FLOAT") {
		   retType = "FLOAT"; 
}
	returnStatementFound = line_count;
	  $2->match = "return " + $2->match + ";";
	  logout<< "at line no:" <<line_count << " statement :  RETURN expression SEMICOLON\n";
	 $$ = new SymbolInfo($2); 
	 if(currentFunction!="main") {
	 $$->code += "pop bp\n";
	  $$->code+="ret\n";
	}
	  logout <<  endl; logout << $$->match<<endl;
	  }
	  | RETURN expression error
	  {
	
	  if($2->getIdentifierType()=="VARIABLE" && $2->varInfo.variableType == "INT") 
	 retType=="INT";
	  else if ($2->getIdentifierType()=="VARIABLE" && $2->varInfo.variableType == "FLOAT") 	   retType = "FLOAT"; 
	  else  if($2->getIdentifierType()=="FUNCTION" && $2->funcInfo.returnType == "INT") {

	 retType="INT";
}
	  else if ($2->getIdentifierType()=="FUNCTION" && $2->funcInfo.returnType == "FLOAT") {
		   retType = "FLOAT"; 
}
else  if($2->getIdentifierType()=="ARRAY" && $2->arrInfo.arrayType == "INT") {

	 retType="INT";
}
	  else if ($2->getIdentifierType()=="ARRAY" && $2->arrInfo.arrayType == "FLOAT") {
		   retType = "FLOAT"; 
}
	returnStatementFound = line_count;
	  $1->match = "return " + $2->match ;
	  logout<< "at line no:" <<line_count << " statement :  RETURN expression error\n";
	 $$ = new SymbolInfo($1); 
      logout <<  endl; logout << $$->match<<endl;
	  }
	  | error SEMICOLON
	  {
	  logout<< "at line no:" <<line_count << " statement :  error SEMICOLON\n";
	  $$ = new SymbolInfo($1);
	  }
	  | error LCURL
	  {
	 logout<< "at line no:" <<line_count << " statement :  error LCURL\n";
	 $$ = new SymbolInfo($1);
	  }
	  ;
	  
expression_statement 	: SEMICOLON
	{
	  
	  logout<< "at line no:" <<line_count << " expression_statement : SEMICOLON\n";
	 
	  $$->match = ";";
	  $$=new SymbolInfo(";","SEMICOLON");
							$$->code="";
	  logout <<  endl; logout << $$->match << endl;
	
	}			
			| expression SEMICOLON 
	
	{
	  $1->match+=";";
	  $$ = new SymbolInfo($1); 
	  logout<< "at line no:" <<line_count << " expression_statement : expression SEMICOLON \n";
	  logout <<  endl; logout << $$->match << endl;
	
	}
		| expression error 
	
	{
	// syntactic_errors++;
	  
	  $$ = new SymbolInfo($1); 
	  logout<< "at line no:" <<line_count << " expression_statement : expression error \n";
	//  errout<< endl; errout<< "at line no:" <<line_count << " semicolon missing \n";
	  logout <<  endl; logout << $$->match << endl;
	
	}
			;
	  
variable : ID			 		
{ 
		
			SymbolInfo *s = table.LookUp($1->getSymbolName());
			if(s==NULL) {
			semantic_errors++;
			errout<< endl; errout<< "Error at line no: " <<line_count << " Variable: " <<$1->getSymbolName()<<" not declared\n";
			//ostringstream oss;
			//oss<<table.currentScope->id;			
			s = new SymbolInfo( $1->getSymbolName(),"ID");

			s->setIdentifierType("VARIABLE");
			s->match = $1->getSymbolName();
			}
			else if(s->getIdentifierType()=="ARRAY") {
			semantic_errors++;
			errout<< endl; errout<< "Error at line no: " <<line_count << " Array: " <<$1->getSymbolName()<<" used without index\n";			
			}
			else if(s->getIdentifierType()=="FUNCTION") {
			semantic_errors++;
			errout<< endl; errout<< "Error at line no: " <<line_count << " Function: " <<$1->getSymbolName()<<" used as a variable\n";			
			}
			
			$$ = new SymbolInfo(s);
			//errout << $$->printSymbol() << endl;
			ostringstream oss;
			oss<<table.currentScope->id;
			//cout << oss.str() << "   " << s->getSymbolName()<<" " << s->getAssemblyName() << "   "<< endl;
			$$->setSymbolName(s->getAssemblyName());
			$$->match = $1->getSymbolName();
			$$->code = "";
			codedebug<< "at line no:" <<line_count << " variable : ID\n";
			logout <<  endl; logout << $$->match << endl;
				codedebug << $$->code;
}		
	 | ID LTHIRD expression RTHIRD  
{ 			SymbolInfo *s = table.LookUp($1->getSymbolName());
			if(s == NULL){
				s = new SymbolInfo( $1->getSymbolName(),"ID");
				s->setIdentifierType("ARRAY");
				semantic_errors++;
				errout<< endl; errout<< "Error at line no: " <<line_count << " Array " << $1->getSymbolName()<<" is not declared\n";			
				}
			else if(s->getIdentifierType()=="ARRAY"){
			
			int val;
			
					if($3->getSymbolType()=="CONST_INT") {val = atoi($3->getSymbolName().c_str());}
					else if($3->getSymbolType()=="CONST_FLOAT") {
					val =99999;
					semantic_errors++;
					errout<< endl; errout<< "Error at line no: " <<line_count << " Array index cannot be floating point\n";	
					}
					else if ($3->getSymbolType()=="ID" && $3->getIdentifierType()=="VARIABLE" && $3->varInfo.variableType 						== "INT") val = $3->varInfo.ival;
						else if ($3->getSymbolType()=="ID" && $3->getIdentifierType()=="VARIABLE" && $3->varInfo.variableType 						== "FLOAT") {
					val =99999;
semantic_errors++;
					errout<< endl; errout<< "Error at line no: " <<line_count << " Array index cannot be floating point\n";	
					} 
					if(val >= $1->arrInfo.arraySize && val!=99999 ) {
//semantic_errors++;
				//	errout<< endl; errout<< "Error at line no:" <<line_count << " array index out of bounds\n";	
					}
					else if(val < 0) 
					{
semantic_errors++;
					errout<< endl; errout<< "Error at line no: " <<line_count << " Array index cannot be negative\n";	
					}
					else s->arrInfo.arrayIndex = val;
					
					
					
					}
					else {semantic_errors++; errout<< endl; errout<< "Error at line no: " <<line_count << " Index used with non-array datatype\n";}	
					if($3->funcInfo.returnType == "VOID" && lineOfVoid!=line_count) {lineOfVoid = line_count; semantic_errors++; errout<< endl; errout<< "Error at line no: " <<line_count << " VOID return type cannot be called as a part of an expression\n";}	
			s->match = $1->getSymbolName() + "["+ $3->match + "]";
			$$ = new SymbolInfo(s);
			ostringstream oss;
			oss<<table.currentScope->id;	
			$$->setSymbolName(s->getAssemblyName());
		
			//dataList.push_back($$);
			string str = string(newTemp());
			$$->code=$3->code+"mov bx," +$3->getSymbolName() +"\nadd bx,bx\n";
			codedebug << "at line no:" <<line_count << " variable : ID LTHIRD expression RTHIRD\n";
			codedebug << $$->code;
			logout<< "at line no:" <<line_count << " variable : ID LTHIRD expression RTHIRD\n";
			logout <<  endl; logout << $$->match << endl;
}
	 ;
	 
 expression : logic_expression
            {
           //rulesCount++;;;
	    logout<< "at line no:" <<line_count << "  expression : logic_expression\n";
	    $$ = new SymbolInfo($1); logout <<  endl; logout << $$->match<<endl;
	    codedebug << "at line no:" <<line_count << " expression : logic_expression\n";
			codedebug << $$->code;
            }	
	   | variable ASSIGNOP logic_expression
	   {
		
		if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "VARIABLE") {
			 if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "FLOAT")	{
				
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting float to int \n";
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "INT")	{
				
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting int to float \n";

				
				}
		
		}
if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "FUNCTION") {
			if($3->funcInfo.returnType == "VOID" && line_count!=lineOfVoid) {
			semantic_errors++;
			errout<< endl; errout << "Error at line no: "<< line_count << " VOID return type cannot be called as a part of expression\n";
		}
			 if($1->varInfo.variableType == "INT"&& $3->funcInfo.returnType == "FLOAT")	{
				
				
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting float to int\n";
				}
else if($1->varInfo.variableType == "FLOAT"&& $3->funcInfo.returnType == "INT")	{
				
				
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting int to float\n";
				}
			

		}
		else if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "ARRAY") {
		if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting float to int\n";
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting int to float\n";
				}
		
				 

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "VARIABLE") {
		 if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting float to int\n";
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting int to float\n";
				}
		}
else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "FUNCTION") {
if($3->funcInfo.returnType == "VOID" && lineOfVoid!=line_count) {
		semantic_errors++;
			errout<< endl; errout << "Error at line no: "<< line_count << " VOID return type cannot be called as a part of expression\n";
		}
		if($1->arrInfo.arrayIndex < $1->arrInfo.arraySize) {
			if($1->varInfo.variableType == "INT"&& $3->funcInfo.returnType == "FLOAT")	{
				
				
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting float to int\n"; 
					
				}
	if($1->varInfo.variableType == "FLOAT"&& $3->funcInfo.returnType == "INT")	{
				
				
				semantic_errors++;
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting int to float\n"; 
					
				}
			
				}
				

		}
		
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "ARRAY") {
		
		
			
			 if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting int to float\n";
				
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				errout<< endl; errout << "Error at line no: "<< line_count << " Type Mismatch for assignment operator : casting float to int\n";
				}
		
			

		}
		$$ = new SymbolInfo($1);
			$$->code=$3->code+$1->code;
			if($3->getIdentifierType()!="FUNCTION")
			$$->code+="mov ax,"+$3->getSymbolName()+"\n";
			if($$->getIdentifierType()=="VARIABLE"){ 
					$$->code+= "mov "+$1->getSymbolName()+",ax\n";
				}
				
				else if($$->getIdentifierType()=="ARRAY"){
					$$->code+= "mov "+$1->getSymbolName()+"[bx],ax\n";
				}
				delete $3;
		 $$->match =$1->match + "=" +$3->match;
	    logout<< "at line no:" <<line_count << "  expression : variable ASSIGNOP logic_expression\n";
	    logout <<  endl; logout << $$->match << endl;

	     codedebug<< "at line no:" <<line_count << "  expression : variable ASSIGNOP logic_expression\n";
	    logout <<  endl; codedebug << $$->code << endl;

	    } 	
	   ;
			
logic_expression : rel_expression
		{
		//rulesCount++;;;
		logout<< "at line no:" <<line_count << "logic_expression : rel_expression\n";
		$$ = new SymbolInfo($1); logout <<  endl; logout << $$->match<<endl;

			codedebug<< "at line no:" <<line_count << "logic_expression : rel_expression\n";
		 logout <<  endl; codedebug << $$->code<<endl;
		} 	
		 | rel_expression LOGICOP rel_expression
		 { 
	if($1->getIdentifierType() == "FUNCTION") {if($1->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
	lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}
if($3->getIdentifierType() == "FUNCTION") { 
if($3->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}
		
		SymbolInfo *s = new SymbolInfo("0","CONST_INT");
		$$=s;
		$$->code=$1->code;
		$$->code+=$3->code;
		$$->match = $1->match + $2->getSymbolName() + $3->match ;
		if($2->getSymbolName()=="&&")// && $1->getIdentifierType()!="FUNCTION" && $3->getIdentifierType()!="FUNCTION")
		{
			$$->code+="mov ax," + $1->getSymbolName()+"\n";
			$$->code+="cmp ax,0\n";
			char *label1 = newLabel();
			$$->code+="je " + string(label1)+"\n";
			$$->code+="mov ax," + $3->getSymbolName()+"\n";
			$$->code+="cmp ax,0\n";
			$$->code+="je " + string(label1)+"\n";
			char *tempVar = newTemp();
			$$->code+="mov " + string(tempVar)+",1\n";
			char *label2 = newLabel();
			$$->code+="jmp " + string(label2)+"\n";
			$$->code+= string(label1)+":\n";
			$$->code+="mov " + string(tempVar)+",0\n";
			$$->code+= string(label2) + ":\n";
			$$->setSymbolName( string(tempVar));
			
		}
		else if($2->getSymbolName()=="||")//&& $1->getIdentifierType()!="FUNCTION" && $3->getIdentifierType()!="FUNCTION")
		{
			$$->code+="mov ax," + $1->getSymbolName()+"\n";
			$$->code+="cmp ax,1\n";
			char *label1 = newLabel();
			$$->code+="je " + string(label1)+"\n";
			$$->code+="mov ax," + $3->getSymbolName()+"\n";
			$$->code+="cmp ax,1\n";
			$$->code+="je " + string(label1)+"\n";
			char *tempVar = newTemp();
			$$->code+="mov " + string(tempVar)+",0\n";
			char *label2 = newLabel();
			$$->code+="jmp " + string(label2)+"\n";
			$$->code+= string(label1)+":\n";
			$$->code+="mov " + string(tempVar)+",1\n";
			$$->code+= string(label2) + ":\n";
			$$->setSymbolName(string(tempVar));
			
		}
		

		delete $3;
		logout<< "at line no:" <<line_count << "logic_expression : rel_expression LOGICOP rel_expression\n";
		logout <<  endl; logout << $$->match << endl;

			codedebug<< "at line no:" <<line_count << "logic_expression : rel_expression LOGICOP rel_expression\n";
		logout <<  endl; logout << $$->code << endl;
		
		 }	
		 ;
			
rel_expression : simple_expression 
		{
		//rulesCount++;;;
		logout<< "at line no:" <<line_count << "rel_expression : simple_expression \n";
		$$ = new SymbolInfo($1); logout <<  endl; logout << $$->match<<endl;

				codedebug<< "at line no:" <<line_count << "rel_expression : simple_expression \n";
		codedebug <<  endl; codedebug << $$->code<<endl;
		}
		| simple_expression RELOP simple_expression
		
		{
	if($1->getIdentifierType() == "FUNCTION") {if($1->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
	lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}
if($3->getIdentifierType() == "FUNCTION") {if($3->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}
        
		SymbolInfo *s = new SymbolInfo("0","CONST_INT");
		$$=s;
		$$->code=$1->code;
		$$->code+=$3->code;
		$$->code+="mov ax," + $1->getSymbolName()+"\n";
				$$->code+="cmp ax," + $3->getSymbolName()+"\n";
		
			
				char *temp=newTemp();
				char *label1=newLabel();
				char *label2=newLabel();
				if($2->getSymbolName()=="<"){
					$$->code+="jl " + string(label1)+"\n";
				}
				else if($2->getSymbolName()=="<="){
					$$->code+="jle " + string(label1)+"\n";
				}
				else if($2->getSymbolName()==">"){
					$$->code+="jg " + string(label1)+"\n";
				}
				else if($2->getSymbolName()==">="){
					$$->code+="jge " + string(label1)+"\n";
				}
				else if($2->getSymbolName()=="=="){
					$$->code+="je " + string(label1)+"\n";
				}
				else if($2->getSymbolName()=="!="){
					$$->code+="jne " + string(label1)+"\n";
				}
				
				$$->code+="mov "+string(temp) +",0\n";
				$$->code+="jmp "+string(label2) +"\n";
				$$->code+= string(label1)+":\nmov "+string(temp)+",1\n";
				$$->code+=string(label2)+":\n";
				$$->setSymbolName(string(temp));
				delete $3;
		$$->match = $1->match + $2->getSymbolName() + $3->match;
		logout<< "at line no:" <<line_count << "rel_expression	: simple_expression RELOP simple_expression \n";
		logout <<  endl; logout << $$->match << endl;

				codedebug<< "at line no:" <<line_count << "rel_expression	: simple_expression RELOP simple_expression \n";
		logout <<  endl; codedebug << $$->match << endl;
		
		}
			
		;
				
simple_expression : term 
		{
		//rulesCount++;;;
		logout<< "at line no:" <<line_count << " simple_expression : term \n";
			codedebug<< "at line no:" <<line_count << " simple_expression : term \n";
		$$ = new SymbolInfo($1); logout <<  endl; codedebug << $$->code<<endl;
		}
		  | simple_expression ADDOP term
		{
if($1->getIdentifierType() == "FUNCTION") {if($1->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}

	}

if($3->getIdentifierType() == "FUNCTION") {if($3->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}
	if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "FUNCTION") {
			if($1->varInfo.variableType == "INT"&& $3->funcInfo.returnType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->funcInfo.returnType== "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->funcInfo.returnType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->funcInfo.returnType== "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}

else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "VARIABLE") {
			if($3->varInfo.variableType == "INT"&& $1->funcInfo.returnType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->varInfo.variableType == "INT"&& $1->funcInfo.returnType== "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->funcInfo.returnType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->funcInfo.returnType== "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}

else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "FUNCTION") {
			if($3->funcInfo.returnType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->funcInfo.returnType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($3->funcInfo.returnType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($3->funcInfo.returnType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}

else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "ARRAY") {
			if($1->funcInfo.returnType == "INT"&& $3->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->funcInfo.returnType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->funcInfo.returnType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->funcInfo.returnType == "FLOAT"&& $3->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "FUNCTION") {
			if($1->funcInfo.returnType == "INT"&& $3->funcInfo.returnType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->funcInfo.returnType == "INT"&& $3->funcInfo.returnType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->funcInfo.returnType == "FLOAT"&& $3->funcInfo.returnType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->funcInfo.returnType == "FLOAT"&& $3->funcInfo.returnType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}

		if($2->getSymbolName()=="+")
	{
		if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "VARIABLE") {
			if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "ARRAY") {
			if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "VARIABLE") {
			if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "ARRAY") {
			if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		
		}
		else if($2->getSymbolName()=="-")
		{
		if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "VARIABLE") {
			if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "ARRAY") {
			if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "VARIABLE") {
			if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "ARRAY") {
			if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "INT")	{
			;
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
	}
		$$->match = $1->match+ $2->getSymbolName() + $3->match;
		$$->code = $1->code;
		$$->code+=$3->code;
		char *tempVar = newTemp();
		$$->code+="mov ax,"+ $1->getSymbolName()+"\n";
		if($2->getSymbolName()=="+") $$->code+="add ax,"+ $3->getSymbolName()+"\n";
		else if($2->getSymbolName()=="-") $$->code+="sub ax,"+ $3->getSymbolName()+"\n";
		$$->code+="mov "+string(tempVar)+",ax\n";
		$$->setSymbolName(string(tempVar));
		logout<< "at line no:" <<line_count << " simple_expression : simple_expression ADDOP term \n";
		logout <<  endl; logout << $$->match << endl;

				codedebug<< "at line no:" <<line_count << " simple_expression : simple_expression ADDOP term \n";
		logout <<  endl; codedebug << $$->code << endl;
		}  
		  ;
					
term : unary_expression
	{
	//rulesCount++;;;
	logout<< "at line no:" <<line_count << " term :	unary_expression\n";
	$$ = new SymbolInfo($1); logout <<  endl; logout << $$->match <<endl;

	codedebug<< "at line no:" <<line_count << " term :	unary_expression\n";
codedebug <<  endl; codedebug << $$->code <<endl;
	}
     |  term MULOP unary_expression
	{
	if($1->getIdentifierType() == "FUNCTION") {if($1->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
	lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}
if($3->getIdentifierType() == "FUNCTION") {if($3->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}
	if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "FUNCTION") {
			if($1->varInfo.variableType == "INT"&& $3->funcInfo.returnType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->funcInfo.returnType== "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->funcInfo.returnType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->funcInfo.returnType== "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}

else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "VARIABLE") {
			if($3->varInfo.variableType == "INT"&& $1->funcInfo.returnType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->varInfo.variableType == "INT"&& $1->funcInfo.returnType== "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->funcInfo.returnType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->funcInfo.returnType== "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}

else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "FUNCTION") {
			if($3->funcInfo.returnType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->funcInfo.returnType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($3->funcInfo.returnType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($3->funcInfo.returnType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}

else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "ARRAY") {
			if($1->funcInfo.returnType == "INT"&& $3->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->funcInfo.returnType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->funcInfo.returnType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->funcInfo.returnType == "FLOAT"&& $3->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "FUNCTION") {
			if($1->funcInfo.returnType == "INT"&& $3->funcInfo.returnType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->funcInfo.returnType == "INT"&& $3->funcInfo.returnType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->funcInfo.returnType == "FLOAT"&& $3->funcInfo.returnType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}
			else if($1->funcInfo.returnType == "FLOAT"&& $3->funcInfo.returnType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_FLOAT");
				$$=s;
				}

		}
	if($2->getSymbolName()=="*")
	{
		if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "VARIABLE") {
			if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "ARRAY") {
			if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "VARIABLE") {
			if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "ARRAY") {
			if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		
		}
		
		else if($2->getSymbolName()=="/")
		{
		if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "VARIABLE") {
			if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "ARRAY") {
			if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "VARIABLE") {
			if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
			
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "ARRAY") {
			if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
				
				SymbolInfo *s = new SymbolInfo("0.0","CONST_FLOAT");
				$$=s;
				}

		}
	}
	else if($2->getSymbolName()=="%")
		{
		if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "VARIABLE") {
			if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "INT")	{
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->varInfo.variableType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->varInfo.variableType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}
		else if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "ARRAY") {
			if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($1->varInfo.variableType == "INT"&& $3->arrInfo.arrayType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
			else if($1->varInfo.variableType == "FLOAT"&& $3->arrInfo.arrayType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "VARIABLE") {
			if($3->varInfo.variableType == "INT" && $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->varInfo.variableType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
			else if($3->varInfo.variableType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}
		else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "ARRAY") {
			if($3->arrInfo.arrayType == "INT" && $1->arrInfo.arrayType == "INT")	{
				
				SymbolInfo *s = new SymbolInfo("0","CONST_INT");
				$$=s;
					
				}
			else if($3->arrInfo.arrayType == "INT"&& $1->arrInfo.arrayType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
			else if($3->arrInfo.arrayType == "FLOAT"&& $1->arrInfo.arrayType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}
	else if($1->getIdentifierType() == "VARIABLE" && $3->getIdentifierType() == "FUNCTION") {
		
			 if($1->varInfo.variableType == "INT"&& $3->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else	 if($1->varInfo.variableType == "FLOAT"&& $3->funcInfo.returnType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else	 if($1->varInfo.variableType == "FLOAT"&& $3->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}
else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "VARIABLE") {
		
			 if($3->varInfo.variableType == "INT"&& $1->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else	 if($3->varInfo.variableType == "FLOAT"&& $1->funcInfo.returnType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else	 if($3->varInfo.variableType == "FLOAT"&& $1->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}

else if($1->getIdentifierType() == "ARRAY" && $3->getIdentifierType() == "FUNCTION") {
		
			 if($1->arrInfo.arrayType == "INT"&& $3->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else if($1->arrInfo.arrayType == "FLOAT"&& $3->funcInfo.returnType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else if($1->arrInfo.arrayType== "FLOAT"&& $3->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}

else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "ARRAY") {
		
			 if($3->arrInfo.arrayType == "INT"&& $1->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else if($3->arrInfo.arrayType == "FLOAT"&& $1->funcInfo.returnType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else if($3->arrInfo.arrayType== "FLOAT"&& $1->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}
		else if($1->getIdentifierType() == "FUNCTION" && $3->getIdentifierType() == "FUNCTION") {
		
			 if($3->funcInfo.returnType == "INT"&& $1->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else if($3->funcInfo.returnType == "FLOAT"&& $1->funcInfo.returnType == "INT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				}
		else if($3->funcInfo.returnType == "FLOAT"&& $1->funcInfo.returnType == "FLOAT")	{
semantic_errors++;
				errout<< endl; errout<< "Error at line no: " << line_count << " MOD operator cannot be used with floating point \n";
				
				}

		}
	}
	$$->code =";"+$1->match + $2->getSymbolName() + $3->match+"\n";
	//$$->code += ";in mulop\n";

			$$->code +=$1->code;
			//$$->code += ";in secondoperand\n";
			$$->code += $3->code;
				//$$->code += ";make ax and bx\n";
			$$->code += "mov ax,"+ $1->getSymbolName()+"\n";
			$$->code += "mov bx,"+ $3->getSymbolName() +"\n";
			char *temp=newTemp();
			if($2->getSymbolName()=="*"){
				$$->code += "mul bx\n";
				$$->code += "mov "+ string(temp) + ",ax\n";
			}
			else if($2->getSymbolName()=="/"){
				$$->code += "xor dx,dx\n";
				$$->code += "div bx\n";
				$$->code += "mov " + string(temp) + ",ax\n";
			}
			else if($2->getSymbolName()=="%"){
				$$->code += "xor dx,dx\n";
				$$->code += "div bx\n";
				$$->code += "mov " + string(temp) + ",dx\n";
				
			}
			$$->setSymbolName( string(temp));
	logout<< "at line no:" <<line_count << " term :	term MULOP unary_expression\n";
	logout <<  endl; logout << $$->match << endl;

		codedebug<< "at line no:" <<line_count << " term :	term MULOP unary_expression\n";
	logout <<  endl; codedebug << $$->code << endl;
	
	}
     ;

unary_expression : ADDOP unary_expression 
	{
	if($2->getIdentifierType() == "FUNCTION") {
	if($2->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
	lineOfVoid = line_count; 
	semantic_errors++;
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}

	$2->match = $1->getSymbolName()+$2->match;
	$$ = new SymbolInfo($2);
	if($1->getSymbolName()=="-") {
		$$->code += "mov ax," + $2->getSymbolName() + "\n";
		$$->code += "neg ax\n";
	if($2->getSymbolType()!="CONST_INT" && $2->getSymbolType()!="CONST_FLOAT"  )	$$->code += "mov " + $2->getSymbolName() + ",ax\n";
	else {
		string str = string(newTemp());
		 $$->code += "mov " + str + ",ax\n";
		 $$->setSymbolName(str);
}
	}
	logout<< "at line no:" <<line_count << " unary_expression : ADDOP unary_expression\n";
	 logout <<  endl; logout << $$->match <<endl;
	} 
	| NOT unary_expression
        {
	if($2->getIdentifierType() == "FUNCTION") {
	if($2->funcInfo.returnType == "VOID"&& lineOfVoid!=line_count) {
	semantic_errors++;
	lineOfVoid = line_count; 
errout<< endl; errout << "Error at line no: " << line_count << " VOID return type cannot be called as a part of an expression\n";}
	}
	
	SymbolInfo *s = new SymbolInfo("0","CONST_INT");
	s->match = "!"+$2->match;
	$$ = new SymbolInfo(s);
	$$->code = $2->code;
	char *temp=newTemp();
	string label1 = string(newLabel());
	string label2 = string(newLabel());
	//$$->code+= ";start\n";
	$$->code+="mov ax," + $2->getSymbolName() + "\n";
	$$->code+="cmp ax,0\n";
	$$->code+="je "+ label1 +"\n";
	$$->code+= "mov "+string(temp)+",0\n";
	$$->code+="jmp "+ label2 +"\n";
	$$->code+= label1 + ":\n";
	$$->code+= "mov "+string(temp)+",1\n";
	$$->code+= label2 + ":\n";
	//$$->code+= ";end\n";

	$$->setSymbolName(string(temp));
	codedebug<< "at line no:" <<line_count << " unary_expression : NOT unary_expression\n";
	codedebug << $$->code;
	logout <<  endl; logout << $$->match << endl;
	
	} 
		 | factor
	{
	//rulesCount++;;; 
	logout<< "at line no:" <<line_count << " unary_expression : factor\n";
	codedebug<< "at line no:" <<line_count << " unary_expression : factor\n";
	$$ = new SymbolInfo($1); logout <<  endl; 
	codedebug << $$->code <<endl;
	
	} 
		 ;
	
factor	: variable 
	{
	if($1->getIdentifierType()=="ARRAY"){
				char *temp= newTemp();
				$$->code+="mov ax," + $1->getSymbolName() + "[bx]\n";
				$$->code+= "mov " + string(temp) + ",ax\n";
				$$->setSymbolName(string(temp));

			}
	logout<< "at line no:" <<line_count << " factor : variable\n";
	codedebug<< "at line no:" <<line_count << " factor : variable\n";
	
	codedebug << $$->code << endl;
	$$ = new SymbolInfo($1); logout <<  endl; logout << $$->match <<endl;
	}
	| ID LPAREN argument_list RPAREN
	{
	$$ = new SymbolInfo($1);
	if($1->getSymbolName()!="println") {
	
	for(int i=argumentsPassed.size()-1;i>=0;i--) {
	$$->code += parametersPassed[i].code;
	$$-> code += "mov ax,"+parametersPassed[i].getSymbolName()+"\n";
	$$-> code += "push ax\n";
	}
	$$->code += "call "+$1->getSymbolName()+"\n";
	ostringstream oss;
	oss << argumentsPassed.size()*2;
	$$->code += "add sp,"+oss.str()+ "\n";
	string s1 = string(newTemp());
	$$->code += "mov "+s1+",ax\n";
	$$->setSymbolName(s1);
}
else {
	  $$ = new SymbolInfo(); 
	  $$->match = "println (" + $3->getSymbolName() + ");";
	  logout <<  endl; logout << $$->match<<endl;
	  $$->code = $3->code;
	  $$->code += "mov ax," + $3->getSymbolName() +"\n";
	  $$->code += "call DECIMAL_OUT\n";
	  $$->code += "mov ah,2\n";
	  $$->code += "mov dl,0dh\n";
	  $$->code += "int 21h\n";
	  $$->code += "mov dl,0ah\n";
	  $$->code += "int 21h\n";
}
	SymbolInfo *s = table.LookUp($1->getSymbolName());
	
	if(s==NULL) {
	semantic_errors++; errout<< endl; errout<< "Error at line no: " <<line_count << " function " << $2->getSymbolName()<< " is not declared" <<endl;
	}
	else if (s->getIdentifierType()!="FUNCTION") {semantic_errors++;  errout<< endl; errout<< "Error  at line no: " <<line_count << " Identifier " << $2->getSymbolName()<< " cannot be used as a function" <<endl;}
	else if (s->getIdentifierType()=="FUNCTION") {
	//if(s->funcInfo.returnType == "VOID") lineOfVoid = line_count;
	if(s->funcInfo.isAlreadyDefined == false) {
	semantic_errors++;  errout<< endl; errout<< "Error at line no: " <<line_count << " function " << $2->getSymbolName()<< " is not defined" <<endl;
	}
	if(argumentsPassed.size()!=s->parameters.size()) {
		semantic_errors++; 
		argumentsPassed.clear();
		errout<< endl; errout<< "Error at line no: " <<line_count << " No of arguments passed to function " << $2->getSymbolName() <<"  mismatch" <<endl;}
	else {
	
	for(int i=0;i<argumentsPassed.size();i++) 
	{
	if(argumentsPassed[i]!=s->parameters[i].varInfo.variableType) {

	semantic_errors++; errout<< endl; errout<< "Error at line no: " <<line_count << " Type of argument passed to function " <<   $2->getSymbolName() <<" mismatch" <<endl;
	}
	}
	 argumentsPassed.clear();
	}
	}
	

	argumentsPassed.clear();
	parametersPassed.clear();
	logout<< "at line no:" <<line_count << " factor : ID LPAREN argument_list RPAREN\n";
	$1->match = $1->getSymbolName() + "(" + $3->match + ")";
	logout <<  endl; logout << $$->match <<endl;
	codedebug<< "at line no:" <<line_count << " factor : ID LPAREN argument_list RPAREN\n";
	
	codedebug << $$->code << endl;
	}
	| LPAREN expression RPAREN
	{
	$2->match = "("+$2->match+")";
	logout<< "at line no:" <<line_count << " factor : LPAREN expression RPAREN\n";
	$$ = new SymbolInfo($2); logout <<  endl; logout << $$->match <<endl;
	}
	| CONST_INT 
	{
	$1->match = $1->getSymbolName();
	$1->setIdentifierType ("VARIABLE");
	$1->varInfo.setVariableType("INT");
	
	logout<< "at line no:" <<line_count << " factor : CONST_INT\n";
	$$ = new SymbolInfo($1); logout <<  endl; logout << $$->match <<endl;
	}
	| CONST_FLOAT
	{
	$1->match = $1->getSymbolName();
	$1->setIdentifierType ("VARIABLE");
	$1->varInfo.setVariableType("FLOAT");
	
	logout<< "at line no:" <<line_count << " factor : CONST_FLOAT\n";
	$$ = new SymbolInfo($1); logout <<  endl; logout << $$->match <<endl;
	}
	| variable INCOP
	{
	
	$1->match = $1->match+"++";
	logout<< "at line no:" <<line_count << " factor : variable INCOP\n";
	$$ = new SymbolInfo($1);
	if($1->getIdentifierType()!="ARRAY") {
	$$->code += "mov ax," + $$->getSymbolName()+ "\n";
	$$->code += "inc ax\n";
	$$->code += "mov " + $$->getSymbolName() + ",ax\n";
}
else {
	$$->code += "mov ax," + $$->getSymbolName()+ "[bx]\n";
	$$->code += "inc ax\n";
	$$->code += "mov " + $$->getSymbolName() + "[bx],ax\n";
}
	 logout <<  endl; logout << $$->match <<endl;
	} 
	
	| variable DECOP
	{
	
	$1->match = $1->match+"--";
	logout<< "at line no:" <<line_count << " factor : variable INCOP\n";
	$$ = new SymbolInfo($1); 
	if($1->getIdentifierType()!="ARRAY") {
	$$->code += "mov ax," + $$->getSymbolName()+ "\n";
	$$->code += "dec ax\n";
	$$->code += "mov " + $$->getSymbolName() + ",ax\n";
}
else {
	$$->code += "mov ax," + $$->getSymbolName()+ "[bx]\n";
	$$->code += "dec ax\n";
	$$->code += "mov " + $$->getSymbolName() + "[bx],ax\n";
}
	
	logout <<  endl; logout << $$->match <<endl;
	} 
	;
	
argument_list : arguments
		{
		$$ = new SymbolInfo($1); 
		logout<< "at line no:" <<line_count << " argument_list : arguments\n";
		logout <<  endl; logout << $$->match << endl;
		}

			  |{
		$$ = new SymbolInfo("$","$"); 
		$$->match = " ";
		logout<< "at line no:" <<line_count << " argument_list : \n";
	        logout <<  endl; logout << $$->match << endl;
		}
			  ;
	
arguments : arguments COMMA logic_expression
		{
		 	if($3->getIdentifierType()=="VARIABLE")
	       argumentsPassed.push_back($3->varInfo.variableType);
	   else if($3->getIdentifierType()=="ARRAY")
	   	argumentsPassed.push_back($3->arrInfo.arrayType);
	   else 	argumentsPassed.push_back($3->funcInfo.returnType);
		  parametersPassed.push_back($3);
	 	argumentsCount++;;
		$3->match = $1->match + "," + $3->match;
		$$=new SymbolInfo($3);
		logout<< "at line no:" <<line_count << " arguments : arguments COMMA logic_expression\n";
		logout <<  endl; logout << $3->match << endl;
		}
	      | logic_expression
	      {
	      	if($1->getIdentifierType()=="VARIABLE")
	       argumentsPassed.push_back($1->varInfo.variableType);
	   else if($1->getIdentifierType()=="ARRAY")
	   	argumentsPassed.push_back($1->arrInfo.arrayType);
	    else 	argumentsPassed.push_back($1->funcInfo.returnType);
	        parametersPassed.push_back($1);
	       argumentsCount++;;
	       $$ = new SymbolInfo($1); 
	       logout<< "at line no:" <<line_count << " arguments : logic_expression\n";
	      
	       logout <<  endl; logout << $1->match << endl;

	        codedebug<< "at line no:" <<line_count << " arguments : logic_expression\n";
	      
	       logout <<  endl; codedebug << $$->code << endl;
	      }
	      ;
 

%%

int main(int argc,char *argv[])
{

	if((fp=fopen(argv[1],"r"))==NULL)
	{
		logout << "Cannot Open Input File.\n";
		exit(1);
	}
        logout.open("prev_log.txt");
	errout.open("1505031_log.txt");
	debugout.open("1505031_code.asm");
	
     debugfile.open("debugfile.txt");
	 codedebug.open("codedebugging.txt");  
        
	yyin=fp;
	yyparse();
	errout<< endl; errout << "Total errors: " << semantic_errors+syntactic_errors+lexical_errors;
	logout << "Symbol Table : " <<endl;
	logout << table.PrintAllScopeTable() <<endl;
	logout << "Total errors: " << semantic_errors+syntactic_errors<< "  ";
	logout << "Total lines: " << line_count;
	errout<< endl; errout.close();
	logout.close();
	debugout.close();

int count = 0;

    ifstream fin("1505031_code.asm");
    ofstream fout("1505031_optimized_code.asm");
    if(!fin)
    {
        cout << "File problem" << endl ;
        return -1;
    }

    vector<string> qInit ;
    queue<string> qMovOp ;
    for(string line; getline( fin, line ) != 0; )
    {
   //    cout << line << endl ;
   std::stringstream trimmer;


        qInit.push_back(line);
//fout << line<<endl;

    }


   
  for(int j=0;j<qInit.size();j++){
             string nextStr[3];
    string str[3];
      //  cout<<qInit[j]<<endl;
          string moveString;
          string line = qInit[j];
            if(qInit[j].size()>=3){
            for(int i=0;i<3;i++){
                moveString+=line[i];
            }
            }
        if(moveString=="mov")   {
        istringstream tokenStream(line);
        while (getline(tokenStream, line, ' '))
        {


             istringstream tokenStream(line);

             int i=0;
        while (getline(tokenStream, line, ','))
        {

            str[i] = line;
            i++;
        }
        }


            moveString.clear();

          string nextLine = qInit[j+1];
            if(qInit[j+1].size()>=3){
            for(int i=0;i<3;i++){
                moveString+=nextLine[i];
            }
            }
        if(moveString=="mov")   {
        istringstream tokenStream(nextLine);
        while (getline(tokenStream, nextLine, ' '))
        {

             istringstream tokenStream(nextLine);

            int  i=0;
            while (getline(tokenStream, nextLine, ','))
            {
                nextStr[i] = nextLine;
                i++;
            }
        }
       /* cout << "-------printing str --------------------\n";
        for(int i=0;i<3;i++){
            cout << str[i]<<endl;
        }
         cout << "-------printing nextStr --------------------\n";
        for(int i=0;i<3;i++){
            cout << nextStr[i]<<endl;
        }*/
        if(nextStr[0].compare(str[1])==0&&str[0].compare(nextStr[1])==0) {
         
            qInit[j+1] = "";
count++;
        }
        }
            moveString.clear();
    }
    }
cout << "Total lines optimized: " << count;
 for(int i=0;i<qInit.size();i++){
 	string line = qInit[i];
 	
 

 	if(line[0]=='.') 
    fout << qInit[i] <<endl;
else if(line[0]==';') fout << "\t\t" << qInit[i] <<endl;

else  fout << "\t" << qInit[i] <<endl;
 }

fin.close();
fout.close();

	return 0;
}

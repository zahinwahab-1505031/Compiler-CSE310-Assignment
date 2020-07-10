#include<iostream>
#include<fstream>
#include<string.h>
#include<math.h>
#include<stdlib.h>
#include<vector>
#include<queue>
#include<iterator>
#include<set>
#include<istream>
#include <sstream>
#include<algorithm>
using namespace std;
class FunctionInfo
{
public:

    vector<string> arguments;
    string returnType;
    bool isAlreadyDefined;
    FunctionInfo()
    {
	isAlreadyDefined = false;
    }

};

class ArrayInfo
{
public:
    int arraySize;
    string arrayType;
    vector<int> vector_integers;
    vector<float> vector_floats;
    int arrayIndex;
    ArrayInfo()
    {

    }
    void setArraySize(int i)
    {
        this->arraySize = i;
    }
    void setArrayType(string type)
    {
        this->arrayType = type;
    }
};
class VariableInfo
{
public:
    string variableType; //INT,FLOAT,DOUBLE
    int ival;
    float fval;
    VariableInfo()
    {
	ival=0;
	fval=0.0;
    }
    void setVariableType(string type)
    {
        this->variableType = type;
    }
};
class SymbolInfo
{

    string SymbolName;
    string SymbolType;
    string IdentifierType; //FUNC,ARRAY,VAR
 
    
public:
    string code;
    string match;
   string assemblyName;
    vector<SymbolInfo> parameters;
      vector<string> assemblyNames;
    VariableInfo varInfo;
    FunctionInfo funcInfo;
    ArrayInfo arrInfo;
    SymbolInfo* next;
    SymbolInfo(string SymbolName, string SymbolType)
    {
	if(SymbolType == "CONST_INT") {
	this->setIdentifierType("VARIABLE");
	this->varInfo.variableType = "INT";
	this->varInfo.ival = atoi(SymbolName.c_str());
	}
	else if(SymbolType == "CONST_FLOAT") {
	this->setIdentifierType("VARIABLE");
	this->varInfo.variableType = "FLOAT";
	this->varInfo.fval = atof(SymbolName.c_str());
	}
        this->SymbolName = SymbolName;
        this->SymbolType = SymbolType;
        this->next = NULL;
    }
    SymbolInfo(string SymbolName, string SymbolType,string assemblyName)
    {
    
        this->SymbolName = SymbolName;
        this->SymbolType = SymbolType;
        this->assemblyName = assemblyName;
    }
    SymbolInfo()
    {
    }
 SymbolInfo(SymbolInfo *s)
    {
	
    this->SymbolName = s->SymbolName;
	this->assemblyName = s->assemblyName;
    this->SymbolType = s->SymbolType;
    this->next = NULL;
    this->IdentifierType=s->IdentifierType; //FUNC,ARRAY,VAR

    this->match = s->match;
    this->code = s->code;
    this->parameters = s->parameters;
    this->varInfo = s->varInfo;
    this->funcInfo = s->funcInfo;
    this->arrInfo = s->arrInfo;
    }

    string getSymbolName()
    {
        return SymbolName;
    }

    string getSymbolType()
    {
        return SymbolType;
    }
    string getIdentifierType()
    {
        return IdentifierType;
    }
   

    void setSymbolName(string SymbolName)
    {
        this->SymbolName=SymbolName;
    }

    void setSymbolType(string SymbolType)
    {
        this->SymbolType = SymbolType;
    }
    void setIdentifierType(string IdentifierType)
    {
        this->IdentifierType = IdentifierType;
    }
    void setAssemblyName(string name)
    {
        this->assemblyName = name;
    }
    string getAssemblyName()
    {
        return assemblyName;
    }
    string printSymbol(){
        string temp = "name : "+ SymbolName;
        temp += " type :"+  SymbolType;
        temp += " assembly name : "+ assemblyName;
        temp += " id type: "+ IdentifierType;
        return temp;
    }





};

class ScopeTable
{
public:
    SymbolInfo **table;
    ScopeTable* parentScope;
    int id;
    int SIZE;
    ScopeTable(int s,int id)
    {
        SIZE = s;
        table = new SymbolInfo*[SIZE];
        for (int i = 0; i < SIZE; i++)
            table[i] = NULL;

        this->id = id;
        this->parentScope = NULL;
    }
    ~ScopeTable()
    {
        delete []table;
    }


    long Hash(string s)
    {
        /**/
        /*    */
        unsigned long hash = 0;
        int c;
        char *str = new char[s.length() + 1];
        strcpy(str, s.c_str());
        while (c = *str++)
            hash = c + (hash << 6) + (hash << 16) - hash;

        return hash%SIZE;
    }
    bool Insert(string SymbolName,string SymbolType)
    {
        //////cout << "insert er moddhe\n";
        if(LookUp(SymbolName))
        {
            //////cout << "Already found in current scope table\n";
            //  ////fout << "Already found in current scope table\n";
            return false;
        }

        long hashValue;
        hashValue = Hash(SymbolName);
        int pos = 0;

        ////////cout <<SymbolName << "\n";
        SymbolInfo *prev = NULL;
        SymbolInfo *temp = table[hashValue];
        SymbolInfo *newElement = new SymbolInfo (SymbolName,SymbolType);

        if(temp==NULL)
        {

            newElement->next = NULL;
            table[hashValue] = newElement;

            //////cout << "Inserted at ScopeTable#" << id+1<< " position" << hashValue << "," << pos <<endl;
            ////fout << "Inserted at ScopeTable#" << id+1<< " position" << hashValue << "," << pos <<endl;
            return true;

        }
        else
        {
            pos++;
            while (temp->next != NULL)
            {

                temp = temp->next;
                pos++;
            }

            temp->next = newElement;
            newElement->next = NULL;

            //////cout << "Inserted at ScopeTable#" << id+1<< " position  " << hashValue << "," << pos <<endl;
            ////fout << "Inserted at ScopeTable#" << id+1<< " position  " << hashValue << "," << pos <<endl;

            return true;
        }

    }

bool Insert(SymbolInfo *s)
    {
        //////cout << "insert er moddhe\n";
        if(LookUp(s->getSymbolName()))
        {
            //////cout << "Already found in current scope table\n";
            //  ////fout << "Already found in current scope table\n";
            return false;
        }

        long hashValue;
        hashValue = Hash(s->getSymbolName());
        int pos = 0;

        ////////cout <<SymbolName << "\n";
        SymbolInfo *prev = NULL;
        SymbolInfo *temp = table[hashValue];
        SymbolInfo *newElement = new SymbolInfo(s);

        if(temp==NULL)
        {

            newElement->next = NULL;
            table[hashValue] = newElement;

            //////cout << "Inserted at ScopeTable#" << id+1<< " position" << hashValue << "," << pos <<endl;
            ////fout << "Inserted at ScopeTable#" << id+1<< " position" << hashValue << "," << pos <<endl;
            return true;

        }
        else
        {
            pos++;
            while (temp->next != NULL)
            {

                temp = temp->next;
                pos++;
            }

            temp->next = newElement;
            newElement->next = NULL;

            //////cout << "Inserted at ScopeTable#" << id+1<< " position  " << hashValue << "," << pos <<endl;
            ////fout << "Inserted at ScopeTable#" << id+1<< " position  " << hashValue << "," << pos <<endl;

            return true;
        }

    }
    SymbolInfo* LookUp(string SymbolName)
    {
        long hashValue=Hash(SymbolName);
        SymbolInfo *temp = table[hashValue];
        int pos =0;

        if(temp==NULL)
        {
            //  //////cout <<"Not Found" <<endl;
            return temp;
        }
        while (temp != NULL)
        {
            if(SymbolName.compare(temp->getSymbolName())==0)
            {
                string SymbolType = temp->getSymbolType();
                //////cout << "Found in ScopeTable# "<<id+1<<" at position "<<hashValue <<", "<<pos<<endl;
                //    ////fout << "Found in ScopeTable# "<<id+1<<" at position "<<hashValue <<", "<<pos<<endl;
                return temp;
            }
            temp = temp->next;
            pos++;
        }
        //   //////cout <<"Not Found" <<endl;
        return NULL;
    }
    bool Delete(string SymbolName)
    {
        SymbolInfo *temp1 = LookUp(SymbolName);
        if(temp1==NULL)
        {
            //////cout << "Not Found" <<endl;
            ////fout << "Not Found" <<endl;
            return false;
        }
        long hashValue;
        hashValue = Hash(SymbolName);
        SymbolInfo *prev = NULL;
        SymbolInfo *temp = table[hashValue];
        //  if(temp==NULL) return false;
        int pos = 0;
        while (temp != NULL && temp->getSymbolName().compare(SymbolName) != 0)
        {
            prev = temp;
            temp = temp->next;
            pos++;
        }



        if (prev == NULL)
        {
            table[hashValue] = temp->next;
        }
        else
        {
            prev->next=temp->next;
        }
        delete temp;
        //////cout << "Deleted entry at" << hashValue <<"," << pos << "from current ScopeTable"<<endl;
        // ////fout << "Deleted entry at" << hashValue <<"," << pos << "from current ScopeTable"<<endl;
        return true;

    }



    string Print()
    {
	string s;
	ostringstream oss;
	oss<<id+1;
        //cout << "ScopeTable #" <<id+1<<endl;
        s+= "ScopeTable #" + oss.str()+"\n";
        //fprintf(logout, "\nScopeTable # %d\n",id+1);
        
        for(int i=0; i<SIZE; i++)
        {
            if(table[i]==NULL) continue;
            //cout << i << "-->";
	    ostringstream oss;
	    oss<<i;
            s+= oss.str()+"-->";
            ////fout << i << "-->";
            //fprintf(logout, " %d-->",i);
            if(table[i]!=NULL&&table[i]->next==NULL)
            {
               

                //cout <<"< "<< table[i]->getSymbolName() << ":" << table[i]->getSymbolType() << ">";
                s+= "< name: "+ table[i]->getSymbolName() + ":type: " + table[i]->getSymbolType() + " IdentifierType: " + table[i]->getIdentifierType()+": assembly: "+ table[i]->getAssemblyName()+">";
                //fprintf(logout, "< %s:%s >",a1,b1);
            }
            if(table[i]!=NULL&&table[i]->next!=NULL)
            {

                SymbolInfo *temp = table[i];
               
                //////cout <<"<" << temp->getSymbolName() << ":" << temp->getSymbolType() << "> ";
                s+="<name: " + temp->getSymbolName() + ":type: " + temp->getSymbolType() + " IdentifierType : " + temp->getIdentifierType()+": assembly: "+ temp->getAssemblyName()+">";
                //fprintf(logout, "< %s:%s >" ,a1,b1);
                temp = temp->next;
                while(temp!=NULL)
                {  
                    //cout <<"<" << temp->getSymbolName() << ":" << temp->getSymbolType() << "> ";
                    s+="<name: " + temp->getSymbolName() + ":type:" + temp->getSymbolType() + " IdentifierType: " + temp->getIdentifierType()+ ": assembly: "+ temp->getAssemblyName()+">";
                    //fprintf(logout, "< %s:%s >" ,a1,b1);
                    temp = temp->next;
                }

            }
            //cout <<endl;
            //fprintf(logout, "\n");
           s+="\n";
        }
	return s;
        //fprintf(logout, "\n\n");

    }


};

class SymbolTable
{
public:
    ScopeTable* currentScope;
    int size;
    int count;
    SymbolTable(int size)
    {
        currentScope = new ScopeTable(size,0);
        this->size = size;
	count = 0;
    }
    string EnterScope()
    {
        
        count++;
        ScopeTable* temp = new ScopeTable(size,count);
        temp->parentScope = currentScope;
        currentScope = temp;
        //cout <<"New ScopeTable with id "<< count+1<<" is created"<<endl;
        ostringstream oss;
	    oss<<count+1;
        string s="New ScopeTable with id "+ oss.str()+" is created\n";
	return s;
    }
    string ExitScope()
    {
        ScopeTable* temp = currentScope;
        currentScope= currentScope->parentScope;
        //cout << "ScopeTable with id " <<temp->id +1<<" removed"<<endl;
        ostringstream oss;
	oss<<temp->id+1;
        string s="ScopeTable with id "+ oss.str()+" is removed\n";
	
        delete(temp);
	return s;
    }
    bool Insert(string SymbolName,string SymbolType)
    {
        if(currentScope->Insert(SymbolName,SymbolType)) return true;
        else return false;
    }

bool Insert(SymbolInfo *s)
    {
        if(currentScope->Insert(s)) return true;
        else return false;
    }
/*SymbolInfo* InsertAndRet(SymbolInfo *s)
    {
       SymbolInfo *temp = currentScope->InsertAndRet(s);
       return temp;
    }*/
    SymbolInfo *LookUp(string SymbolName)
    {
	////cout << "inside lookup";
        ScopeTable* temp = currentScope;
        SymbolInfo *ptr = NULL;
        while(temp!=NULL)
        {

            ptr = temp->LookUp(SymbolName);
            if(ptr!=NULL) return ptr;
            temp = temp->parentScope;
        }
        if(ptr==NULL)
        {
        //   //cout << "Not Found" <<endl;
            ////fout << "Not Found" <<endl;
        }
        return NULL;
    }
SymbolInfo *LookUpCurrentScope(string SymbolName)
    {
	////cout << "inside lookup";
        ScopeTable* temp = currentScope;
        SymbolInfo *ptr = NULL;
        while(temp!=NULL)
        {

            ptr = temp->LookUp(SymbolName);
            if(ptr!=NULL) return ptr;
            
        }
        if(ptr==NULL)
        {
           //cout << "Not Found" <<endl;
            ////fout << "Not Found" <<endl;
        }
        return NULL;
    }
    bool Remove(string SymbolName)
    {
        if(currentScope->Delete(SymbolName)) return true;
        else return false;
    }
    string PrintCurrentScopeTable()
    {
       return currentScope->Print();
    }
    string PrintAllScopeTable()
    {
        string s;
        ScopeTable* temp = currentScope;
        while(temp!=NULL)
        {
            s+=temp->Print();
            temp = temp->parentScope;
        }
	return s;
    }
};





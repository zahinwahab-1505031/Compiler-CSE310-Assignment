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
ofstream fout("output.txt");
class SymbolInfo
{

    string SymbolName;
    string SymbolType;
public:
    SymbolInfo* next;
    SymbolInfo(string SymbolName, string SymbolType)
    {
        this->SymbolName = SymbolName;
        this->SymbolType = SymbolType;
        this->next = NULL;
    }

    string getSymbolName()
    {
        return SymbolName;
    }

    string getSymbolType()
    {
        return SymbolType;
    }
     void setSymbolName(string SymbolName)
    {
         this->SymbolName=SymbolName;
    }

    void setSymbolType(string SymbolType)
    {
        this->SymbolType = SymbolType;
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
        if(LookUp(SymbolName)) {
           cout << "Already found in current scope table\n";
           fout << "Already found in current scope table\n";
            return false;
            }

        long hashValue;
        hashValue = Hash(SymbolName);
        int pos = 0;

        //cout <<SymbolName << "\n";
        SymbolInfo *prev = NULL;
        SymbolInfo *temp = table[hashValue];
        SymbolInfo *newElement = new SymbolInfo (SymbolName,SymbolType);
        if(temp==NULL)
        {

            newElement->next = NULL;
            table[hashValue] = newElement;

            cout << "Inserted at ScopeTable#" << id+1<< " position" << hashValue << "," << pos <<endl;
            fout << "Inserted at ScopeTable#" << id+1<< " position" << hashValue << "," << pos <<endl;
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

            cout << "Inserted at ScopeTable#" << id+1<< " position  " << hashValue << "," << pos <<endl;
            fout << "Inserted at ScopeTable#" << id+1<< " position  " << hashValue << "," << pos <<endl;

            return true;
        }

    }
    SymbolInfo* LookUp(string SymbolName)
    {
        long hashValue=Hash(SymbolName);
        SymbolInfo *temp = table[hashValue];
        int pos =0;

        if(temp==NULL) {
              //  cout <<"Not Found" <<endl;
                return temp;
        }
        while (temp != NULL)
        {
            if(SymbolName.compare(temp->getSymbolName())==0)
            {
                string SymbolType = temp->getSymbolType();
                cout << "Found in ScopeTable# "<<id+1<<" at position "<<hashValue <<", "<<pos<<endl;
                fout << "Found in ScopeTable# "<<id+1<<" at position "<<hashValue <<", "<<pos<<endl;
                return temp;
            }
            temp = temp->next;
            pos++;
        }
     //   cout <<"Not Found" <<endl;
        return NULL;
    }
    bool Delete(string SymbolName)
    {
        SymbolInfo *temp1 = LookUp(SymbolName);
        if(temp1==NULL) {
                cout << "Not Found" <<endl;
                fout << "Not Found" <<endl;
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
        cout << "Deleted entry at" << hashValue <<"," << pos << "from current ScopeTable"<<endl;
        fout << "Deleted entry at" << hashValue <<"," << pos << "from current ScopeTable"<<endl;
        return true;

    }



    void Print(){
      cout << "ScopeTable #" <<id+1<<endl;
      fout << "ScopeTable #" <<id+1<<endl;
        for(int i=0;i<SIZE;i++){
                cout << i << "-->";
                fout << i << "-->";
            if(table[i]!=NULL&&table[i]->next==NULL) {cout <<"< "<< table[i]->getSymbolName() << ":" << table[i]->getSymbolType() << ">";
            fout <<"< "<< table[i]->getSymbolName() << ":" << table[i]->getSymbolType() << ">";
            }
            if(table[i]!=NULL&&table[i]->next!=NULL){
                    SymbolInfo *temp = table[i];
                    cout <<"<" << temp->getSymbolName() << ":" << temp->getSymbolType() << "> ";
                    fout <<"<" << temp->getSymbolName() << ":" << temp->getSymbolType() << "> ";
                    temp = temp->next;
                while(temp!=NULL){
                     cout <<"<" << temp->getSymbolName() << ":" << temp->getSymbolType() << "> ";
                     fout <<"<" << temp->getSymbolName() << ":" << temp->getSymbolType() << "> ";
                    temp = temp->next;
                }

            }
            cout <<endl;
            fout << endl;
        }
    }


};

class SymbolTable {
  public:
    ScopeTable* currentScope;
    int size;
    SymbolTable(int size){
       currentScope = new ScopeTable(size,0);
       this->size = size;
    }
    void EnterScope(){
        int id;
        id = currentScope->id;
        ScopeTable* temp = new ScopeTable(size,id+1);
        temp->parentScope = currentScope;
        currentScope = temp;
        cout <<"New ScopeTable with id "<< id+2<<" is created"<<endl;
        fout <<"New ScopeTable with id "<< id+2<<" is created"<<endl;
    }
    void ExitScope() {
        ScopeTable* temp = currentScope;
        currentScope= currentScope->parentScope;
        cout << "ScopeTable with id " <<temp->id +1<<" removed"<<endl;
        fout << "ScopeTable with id " <<temp->id +1<<" removed"<<endl;
        delete(temp);
    }
    bool Insert(string SymbolName,string SymbolType){
       if(currentScope->Insert(SymbolName,SymbolType)) return true;
       else return false;
    }
    SymbolInfo *LookUp(string SymbolName) {
        ScopeTable* temp = currentScope;
        SymbolInfo *ptr = NULL;
        while(temp!=NULL){

            ptr = temp->LookUp(SymbolName);
            if(ptr!=NULL) return ptr;
            temp = temp->parentScope;
        }
        if(ptr==NULL){
            cout << "Not Found" <<endl;
            fout << "Not Found" <<endl;
        }
        return NULL;
    }
    bool Remove(string SymbolName){
         if(currentScope->Delete(SymbolName)) return true;
       else return false;
    }
    void PrintCurrentScopeTable(){
        currentScope->Print();
    }
    void PrintAllScopeTable(){
         ScopeTable* temp = currentScope;
        while(temp!=NULL){
            temp->Print();
            temp = temp->parentScope;
        }
    }
};
int main()
{



    ifstream fin("input.txt");

    if(!fin)
    {
        cout << "File problem" << endl ;
        return -1;
    }

    queue<string> qInit ;

    for(string line; getline( fin, line ) != 0; )
    {
     //   cout << line << endl ;
        qInit.push(line);

    }
    printf("--**\n");

    string s = qInit.front();
    qInit.pop();

    queue<string> q;
    string oneString;
    istringstream tokenStream(s);
    while (getline(tokenStream, oneString, ' '))
    {
        q.push(oneString);
    }
  //  printf("-------------******--------------\n");

    stringstream stream(q.front());
    int size;
    stream >> size;
    SymbolTable table(size);
    q.pop();


    int cnt1 = 0;
    while(!qInit.empty())
    {
        s = qInit.front();
        cout <<s<<endl;
        fout <<s <<endl;

        istringstream tokenStream(s);
        while (getline(tokenStream, s, ' '))
        {
            q.push(s);
        }
        int cnt2 = 0;
		string ins;
		string a1;
		string a2;
        while(!q.empty())
        {
          string s1 = q.front();
          if(cnt2==0)  ins = s1;
		  else if(cnt2==1) a1 =s1;
		  else a2 = s1;
            q.pop();
			cnt2++;
        }
		if(ins.compare("I")==0) {table.Insert(a1,a2);}
		else if(ins.compare("L")==0) {table.LookUp(a1);}
		else if(ins.compare("D")==0) {table.Remove(a1);}
		else if(ins.compare("P")==0) {
		if(a1.compare("A")==0) {table.PrintAllScopeTable();}
		else {table.PrintCurrentScopeTable();}
		}
		else if(ins.compare("S")==0) {

                   table.EnterScope();

		}
        else if(ins.compare("E")==0) 	{

               if(table.currentScope->id==0) {
                    table.ExitScope();
                    return 0;
               }
        }
        qInit.pop();
        cnt1++;
    }
    return 0;
}

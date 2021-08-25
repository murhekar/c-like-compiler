#include <iostream>
#include <fstream>
#include <typeinfo>

using namespace std;

#include "common-classes.hh"
#include "error-display.hh"
#include "user-options.hh"
// #include "local-environment.hh"
#include "symbol-table.hh"
#include "ast.hh"
#include "procedure.hh"
#include "program.hh"

int Ast::labelCounter = 0;
int Ast::stringCounter = 0;

Ast::Ast()
{}

Ast::~Ast()
{}

bool Ast::check_ast()
{
	stringstream msg;
	msg << "No check_ast() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

Data_Type Ast::get_data_type()
{
	stringstream msg;
	msg << "No get_data_type() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

Symbol_Table_Entry & Ast::get_symbol_entry()
{
	stringstream msg;
	msg << "No get_symbol_entry() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

bool Ast::is_value_zero()
{
	stringstream msg;
	msg << "No is_value_zero() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

void Ast::set_data_type(Data_Type dt)
{
	stringstream msg;
	msg << "No set_data_type() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

////////////////////////////////////////////////////////////////

Assignment_Ast::Assignment_Ast(Ast * temp_lhs, Ast * temp_rhs, int line)
{
	lhs = temp_lhs;
	rhs = temp_rhs;
	lineno = line;
	ast_num_child = binary_arity;
	node_data_type = void_data_type;
}

Assignment_Ast::~Assignment_Ast()
{
	delete lhs;
	delete rhs;
}

bool Assignment_Ast::check_ast()
{
	CHECK_INVARIANT((rhs != NULL), "Rhs of Assignment_Ast cannot be null");
	CHECK_INVARIANT((lhs != NULL), "Lhs of Assignment_Ast cannot be null");

	// cout << "Reached check_ast for assign" << endl;

	// use typeid(), get_data_type()
	int check = 0;
	if (lhs->get_data_type() == rhs->get_data_type()) {
		++check;
	}
	
	if (check > 0) {
		node_data_type = lhs->get_data_type();
		return true;
	}

	CHECK_INPUT(CONTROL_SHOULD_NOT_REACH, "Assignment statement data type not compatible", lineno);

	return false;
}

void Assignment_Ast::print(ostream & file_buffer)
{
	file_buffer << endl;
	file_buffer << AST_SPACE << "Asgn:" << endl;
	file_buffer << AST_NODE_SPACE << "LHS (";
	lhs->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_NODE_SPACE << "RHS (";
	rhs->print(file_buffer);
	file_buffer << ")";
}

/////////////////////////////////////////////////////////////////

Name_Ast::Name_Ast(string & name, Symbol_Table_Entry & var_entry, int line)
{

	CHECK_INVARIANT((var_entry.get_variable_name() == name),
		"Variable's symbol entry is not matching its name");
	variable_symbol_entry = &var_entry;
	set_data_type(var_entry.get_data_type());
	lineno = line;
	ast_num_child = zero_arity;
}

Name_Ast::~Name_Ast()
{
	delete variable_symbol_entry;
}

Data_Type Name_Ast::get_data_type()
{
	// refer to functions for Symbol_Table_Entry 
	return node_data_type;
}

Symbol_Table_Entry & Name_Ast::get_symbol_entry()
{
	return *variable_symbol_entry;
}

void Name_Ast::set_data_type(Data_Type dt)
{
	node_data_type = dt;
}

void Name_Ast::print(ostream & file_buffer)
{
	file_buffer << "Name : " << variable_symbol_entry->get_variable_name();
}

///////////////////////////////////////////////////////////////////////////////

template <class DATA_TYPE>
Number_Ast<DATA_TYPE>::Number_Ast(DATA_TYPE number, Data_Type constant_data_type, int line)
{
	// use Ast_arity from ast.hh
	constant = number;
	set_data_type(constant_data_type);
	lineno = line;
	ast_num_child = zero_arity;
}

template <class DATA_TYPE>
Number_Ast<DATA_TYPE>::~Number_Ast()
{}

template <class DATA_TYPE>
Data_Type Number_Ast<DATA_TYPE>::get_data_type()
{
	return node_data_type;
}

template <class DATA_TYPE>
void Number_Ast<DATA_TYPE>::set_data_type(Data_Type dt)
{
	node_data_type = dt;
}

template <class DATA_TYPE>
bool Number_Ast<DATA_TYPE>::is_value_zero()
{
	return constant == 0.0;
}

template <class DATA_TYPE>
void Number_Ast<DATA_TYPE>::print(ostream & file_buffer)
{
	file_buffer << "Num : " << constant;
}

///////////////////////////////////////////////////////////////////////////////

Relational_Expr_Ast::Relational_Expr_Ast(Ast * lhs, Relational_Op rop, Ast * rhs, int line)
{
	lhs_condition = lhs;
	rel_op = rop;
	rhs_condition = rhs;
	lineno = line;
	ast_num_child = binary_arity;
	set_data_type(int_data_type);
}

Relational_Expr_Ast::~Relational_Expr_Ast()
{
	delete lhs_condition;
	delete rhs_condition;
}

Data_Type Relational_Expr_Ast::get_data_type()
{
	// refer to functions for Symbol_Table_Entry 
	return node_data_type;
}

void Relational_Expr_Ast::set_data_type(Data_Type dt)
{
	node_data_type = dt;
}

bool Relational_Expr_Ast::check_ast()
{
	CHECK_INVARIANT((rhs_condition != NULL), "Rhs of Relational_Expr_Ast cannot be null");
	CHECK_INVARIANT((lhs_condition != NULL), "Lhs of Relational_Expr_Ast cannot be null");

	// use typeid(), get_data_type()
	int check = 0;
	if (lhs_condition->get_data_type() == rhs_condition->get_data_type()) {
		++check;
	}

	if (check > 0) {
		return true;
	}

	CHECK_INPUT(CONTROL_SHOULD_NOT_REACH, "Relational statement data type not compatible", lineno);

	return false;
}

void Relational_Expr_Ast::print(ostream & file_buffer)
{
	string op_symbol;
	switch(rel_op) {
		case less_equalto:
			op_symbol = "LE";
			break;
		case less_than:
			op_symbol = "LT";
			break;
		case greater_than:
			op_symbol = "GT";
			break;
		case greater_equalto:
			op_symbol = "GE";
			break;
		case equalto:
			op_symbol = "EQ";
			break;
		case not_equalto:
			op_symbol = "NE";
			break;
	}
	file_buffer << endl;
	file_buffer << AST_NODE_SPACE << "Condition: " << op_symbol << endl;
	file_buffer << AST_SUB_NODE_SPACE << "LHS (";
	lhs_condition->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "RHS (";
	rhs_condition->print(file_buffer);
	file_buffer << ")";
}

///////////////////////////////////////////////////////////////////////////////

// TODO data_type ?
Boolean_Expr_Ast::Boolean_Expr_Ast(Ast * lhs, Boolean_Op bop, Ast * rhs, int line)
{
	lhs_op = lhs;
	bool_op = bop;
	rhs_op = rhs;
	lineno = line;
	if (bop == boolean_not) {
		ast_num_child = unary_arity;
		set_data_type(int_data_type);
	} else {
		ast_num_child = binary_arity;
		set_data_type(int_data_type);
	}
}

Boolean_Expr_Ast::~Boolean_Expr_Ast()
{
	delete lhs_op;
	delete rhs_op;
}

Data_Type Boolean_Expr_Ast::get_data_type()
{
	// refer to functions for Symbol_Table_Entry 
	return node_data_type;
}

void Boolean_Expr_Ast::set_data_type(Data_Type dt)
{
	node_data_type = dt;
}

// TODO
bool Boolean_Expr_Ast::check_ast()
{
	// use get_data_type(), typeid()
	// int check = 0;
	// if (lhs->get_data_type() == rhs->get_data_type()) {
	// 	++check;
	// }
	// if (check > 0) {
	// 	return true;
	// }

	return true;

	CHECK_INPUT(CONTROL_SHOULD_NOT_REACH, "Boolean statement data type not compatible", lineno);
}

void Boolean_Expr_Ast::print(ostream & file_buffer)
{
	string op_symbol;
	switch(bool_op) {
		case boolean_not:
			op_symbol = "NOT";
			break;
		case boolean_or:
			op_symbol = "OR";
			break;
		case boolean_and:
			op_symbol = "AND";
			break;
	}
	file_buffer << endl;
	file_buffer << AST_NODE_SPACE << "Condition: " << op_symbol << endl;
	if (op_symbol != "NOT") {
		file_buffer << AST_SUB_NODE_SPACE << "LHS (";
		lhs_op->print(file_buffer);
		file_buffer << ")" << endl;
	}
	file_buffer << AST_SUB_NODE_SPACE << "RHS (";
	rhs_op->print(file_buffer);
	file_buffer << ")";
}

///////////////////////////////////////////////////////////////////////////////

Selection_Statement_Ast::Selection_Statement_Ast(Ast * cond,Ast* then_part, Ast* else_part, int line)
{
	this->cond = cond;
	this->then_part = then_part;
	this->else_part = else_part;
	lineno = line;
	ast_num_child = binary_arity;
}

Selection_Statement_Ast::~Selection_Statement_Ast()
{
	delete cond;
	delete then_part;
	delete else_part;
}

Data_Type Selection_Statement_Ast::get_data_type()
{
	// refer to functions for Symbol_Table_Entry 
	return node_data_type;
}

void Selection_Statement_Ast::set_data_type(Data_Type dt)
{
	node_data_type = dt;
}

// TODO
bool Selection_Statement_Ast::check_ast()
{
	CHECK_INVARIANT((cond != NULL), "Condition of Selection_Statement_Ast cannot be null");
	CHECK_INVARIANT((then_part != NULL), "Then Part of Selection_Statement_Ast cannot be null");
	CHECK_INVARIANT((else_part != NULL), "Else Part of Selection_Statement_Ast cannot be null");

	return true;

	// use typeid(), get_data_type()
	// int check = 0;
	// if (lhs->get_data_type() == rhs->get_data_type()) {
	// 	++check;
	// }
	// cout << typeid(*rhs).name() << " " << typeid(Number_Ast<double>).name() << endl;
	// if ((typeid(*rhs) == typeid(Number_Ast<double>) || typeid(*rhs) == typeid(Number_Ast<int>)) && rhs->is_value_zero()) {
	// 	++check;
	// }
	// if (check > 0) {
	// 	return true;
	// }

	// CHECK_INPUT(CONTROL_SHOULD_NOT_REACH, 
	// 	"Assignment statement data type not compatible", lineno);
}

void Selection_Statement_Ast::print(ostream & file_buffer)
{
	file_buffer << endl;
	file_buffer << AST_SPACE << "IF : " << endl;
	file_buffer << AST_SPACE << "CONDITION (";
	cond->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SPACE << "THEN (";
	then_part->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SPACE << "ELSE (";
	else_part->print(file_buffer);
	file_buffer << ")";
}

/////////////////////////////////////////////////////////////////

Iteration_Statement_Ast::Iteration_Statement_Ast(Ast * cond, Ast* body, int line, bool do_form)
{
	this->cond = cond;
	this->body = body;
	is_do_form = do_form;
	lineno = line;
	ast_num_child = binary_arity;
}

Iteration_Statement_Ast::~Iteration_Statement_Ast()
{
	delete cond;
	delete body;
}

Data_Type Iteration_Statement_Ast::get_data_type()
{
	// refer to functions for Symbol_Table_Entry 
	return node_data_type;
}

void Iteration_Statement_Ast::set_data_type(Data_Type dt)
{
	node_data_type = dt;
}

// TODO
bool Iteration_Statement_Ast::check_ast()
{
	CHECK_INVARIANT((cond != NULL), "Condition of Iteration_Statement_Ast cannot be null");
	CHECK_INVARIANT((body != NULL), "Body of Iteration_Statement_Ast cannot be null");

	return true;

	// use typeid(), get_data_type()
	// int check = 0;
	// if (lhs->get_data_type() == rhs->get_data_type()) {
	// 	++check;
	// }
	// cout << typeid(*rhs).name() << " " << typeid(Number_Ast<double>).name() << endl;
	// if ((typeid(*rhs) == typeid(Number_Ast<double>) || typeid(*rhs) == typeid(Number_Ast<int>)) && rhs->is_value_zero()) {
	// 	++check;
	// }
	// if (check > 0) {
	// 	return true;
	// }

	// CHECK_INPUT(CONTROL_SHOULD_NOT_REACH, 
	// 	"Assignment statement data type not compatible", lineno);
}

void Iteration_Statement_Ast::print(ostream & file_buffer)
{
	if (is_do_form) {
		file_buffer << endl;
		file_buffer << AST_SPACE << "DO (";
		body->print(file_buffer);
		file_buffer << ")" << endl;
		file_buffer << AST_SPACE << "WHILE CONDITION (";
		cond->print(file_buffer);
		file_buffer << ")";
	} else {
		file_buffer << endl;
		file_buffer << AST_SPACE << "WHILE : " << endl;
		file_buffer << AST_SPACE << "CONDITION (";
		cond->print(file_buffer);
		file_buffer << ")" << endl;
		file_buffer << AST_SPACE << "BODY (";
		body->print(file_buffer);
		file_buffer << ")";
	}
	
}

/////////////////////////////////////////////////////////////////

Arithmetic_Expr_Ast::~Arithmetic_Expr_Ast() {
	delete lhs;
	delete rhs;
}

Data_Type Arithmetic_Expr_Ast::get_data_type()
{
	return node_data_type;
}

void Arithmetic_Expr_Ast::set_data_type(Data_Type dt)
{
	node_data_type = dt;
}

bool Arithmetic_Expr_Ast::check_ast()
{

	CHECK_INVARIANT((lhs != NULL), "Lhs of Arithmetic_Expr_Ast cannot be null");

	if (typeid(*this) != typeid(UMinus_Ast)) {
		CHECK_INVARIANT((rhs != NULL), "Rhs of Arithmetic_Expr_Ast cannot be null");
	}

	// use get_data_type(), typeid()
	int check = 0;
	if (lhs->get_data_type() == rhs->get_data_type()) {
		++check;
	}
	if (check > 0) {
		set_data_type(lhs->get_data_type());
		return true;
	} else {
		set_data_type(int_data_type);
	}

	CHECK_INPUT(CONTROL_SHOULD_NOT_REACH, "Arithmetic statement data type not compatible", lineno);

	return false;
}

/////////////////////////////////////////////////////////////////////

Plus_Ast::Plus_Ast(Ast * l, Ast * r, int line)
{
	// set arity and data type
	lhs = l;
	rhs = r;
	lineno = line;
	ast_num_child = binary_arity;
	set_data_type(void_data_type);
}

void Plus_Ast::print(ostream & file_buffer)
{
	file_buffer << endl;
	file_buffer << AST_NODE_SPACE << "Arith: PLUS" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "LHS (";
	lhs->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "RHS (";
	rhs->print(file_buffer);
	file_buffer << ")";
}

/////////////////////////////////////////////////////////////////

Minus_Ast::Minus_Ast(Ast * l, Ast * r, int line)
{
	lhs = l;
	rhs = r;
	lineno = line;
	ast_num_child = binary_arity;
	set_data_type(void_data_type);
}

void Minus_Ast::print(ostream & file_buffer)
{
	file_buffer << endl;
	file_buffer << AST_NODE_SPACE << "Arith: MINUS" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "LHS (";
	lhs->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "RHS (";
	rhs->print(file_buffer);
	file_buffer << ")";
}

//////////////////////////////////////////////////////////////////

Mult_Ast::Mult_Ast(Ast * l, Ast * r, int line)
{
	lhs = l;
	rhs = r;
	lineno = line;
	ast_num_child = binary_arity;
	set_data_type(void_data_type);
}

void Mult_Ast::print(ostream & file_buffer)
{
	file_buffer << endl;
	file_buffer << AST_NODE_SPACE << "Arith: MULT" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "LHS (";
	lhs->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "RHS (";
	rhs->print(file_buffer);
	file_buffer << ")";
}

////////////////////////////////////////////////////////////////////

Divide_Ast::Divide_Ast(Ast * l, Ast * r, int line)
{
	lhs = l;
	rhs = r;
	lineno = line;
	ast_num_child = binary_arity;
	set_data_type(void_data_type);
}

void Divide_Ast::print(ostream & file_buffer)
{
	file_buffer << endl;
	file_buffer << AST_NODE_SPACE << "Arith: DIV" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "LHS (";
	lhs->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "RHS (";
	rhs->print(file_buffer);
	file_buffer << ")";
}

//////////////////////////////////////////////////////////////////////

UMinus_Ast::UMinus_Ast(Ast * l, Ast * r, int line)
{
	lhs = l;
	rhs = r;
	lineno = line;
	ast_num_child = unary_arity;
	set_data_type(lhs->get_data_type());
}

void UMinus_Ast::print(ostream & file_buffer)
{
	file_buffer << endl;
	file_buffer << AST_NODE_SPACE << "Arith: UMINUS" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "LHS (";	
	lhs->print(file_buffer);
	file_buffer << ")";
}

/////////////////////////////////////////////////////////////////

Conditional_Operator_Ast::Conditional_Operator_Ast(Ast* cond, Ast* l, Ast* r, int line)
{
	// set arity and data type
	this->cond = cond;
	lhs = l;
	rhs = r;
	lineno = line;
	ast_num_child = ternary_arity;
	set_data_type(lhs->get_data_type());
}

Conditional_Operator_Ast::~Conditional_Operator_Ast() {
	delete lhs;
	delete rhs;
	delete cond;
}

void Conditional_Operator_Ast::print(ostream & file_buffer)
{
	file_buffer << endl;
	file_buffer << AST_NODE_SPACE << "Arith: Conditional" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "COND (";
	cond->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "LHS (";
	lhs->print(file_buffer);
	file_buffer << ")" << endl;
	file_buffer << AST_SUB_NODE_SPACE << "RHS (";
	rhs->print(file_buffer);
	file_buffer << ")";
}

/////////////////////////////////////////////////////////////////

Sequence_Ast::Sequence_Ast(int line) {
	lineno = line;
}

// TODO
Sequence_Ast::~Sequence_Ast() {
	for (list<Ast*> :: iterator it = statement_list.begin(); it != statement_list.end(); ++it) {
		delete *it;
	}
	// for (list<Icode_Stmt*> :: iterator it = sa_icode_list.begin(); it != sa_icode_list.end(); ++it) {
	// 	delete *it;
	// }
}
 
void Sequence_Ast::ast_push_back(Ast * ast) {
	statement_list.push_back(ast);
}

void Sequence_Ast::print(ostream & file_buffer) {
	file_buffer << endl;
	file_buffer << SA_SPACE << "Sequence Ast:" << endl;
	for (list<Ast*> :: iterator it = statement_list.begin(); it != statement_list.end(); ++it) {
		(*it)->print(file_buffer);
	}
}

/////////////////////////////////////////////////////////////////

String_Ast::String_Ast(string str, Data_Type constant_data_type, int line) {
	const_string = str;
	set_data_type(constant_data_type);
	lineno = line;
	ast_num_child = zero_arity;
}

String_Ast::~String_Ast() {}

Data_Type String_Ast::get_data_type() {
	return node_data_type;
}

void String_Ast::set_data_type(Data_Type dt) {
	node_data_type = dt;
}

void String_Ast::print(ostream & file_buffer) {
	file_buffer << "String : " << const_string;
}

string String_Ast::get_string_label() {
	return string_label;
}

/////////////////////////////////////////////////////////////////

Return_Ast::Return_Ast(string name, Ast* ret, int line) {
	fn_name = name;
	ret_expr = ret;
	if (ret == NULL) {
		set_data_type(void_data_type);
		ast_num_child = zero_arity;
	} else {
		set_data_type(ret->get_data_type());
		ast_num_child = unary_arity;
	}
	lineno = line;
}

Return_Ast::~Return_Ast() {
	delete ret_expr;
}

Data_Type Return_Ast::get_data_type() {
	return node_data_type;
}

void Return_Ast::set_data_type(Data_Type dt) {
	node_data_type = dt;
}

bool Return_Ast::check_ast() {}

void Return_Ast::print(ostream & file_buffer) {
	file_buffer << endl;
	file_buffer << AST_SPACE << "RETURN ";
	if (ret_expr == NULL) {
		file_buffer << "<NOTHING>";
	} else {
		ret_expr->print(file_buffer);
	}
	file_buffer << endl;
}

/////////////////////////////////////////////////////////////////

// Ast * print_ast;
Print_Ast::Print_Ast(Ast* print, int line) {
	print_ast = print;
}

Print_Ast::~Print_Ast() {
	delete print_ast;
}

bool Print_Ast::check_ast() {}

void Print_Ast::print(ostream & file_buffer) {
	file_buffer << endl;
	file_buffer << AST_SPACE << "PRINT: " << endl;
	file_buffer << AST_SUB_NODE_SPACE <<  "expression (";
	print_ast->print(file_buffer);
	file_buffer << ")";
}

/////////////////////////////////////////////////////////////////

// string fn_name;
// Data_Type return_type;
// vector<Ast*> *parameters;
Function_Call_Ast::Function_Call_Ast(Procedure* proc, string name, Data_Type ret_type, vector<Ast*> *params, Symbol_Table& sym_tab, int line) {
	fn_name = name;
	return_type = ret_type;
	parameters = params;
	formal_table = sym_tab;
	this->proc = proc;
}

Function_Call_Ast::~Function_Call_Ast() {
	size_t i, sz = parameters->size();
	for (i = 0; i < sz; ++i) {
		delete (*parameters)[i];
	}
	parameters->clear();
}

// Return Type of function
Data_Type Function_Call_Ast::get_data_type() {
	return return_type;
}

bool Function_Call_Ast::check_ast() {}

void Function_Call_Ast::print(ostream & file_buffer) {
	file_buffer << endl;
	file_buffer << AST_SPACE << "FN CALL: " << fn_name << "(";
	size_t i, sz;
	if (parameters == NULL) {
		sz = 0;
	} else {
		sz = parameters->size();
	}
	for (i = 0; i < sz; ++i) {
		file_buffer << endl << AST_NODE_SPACE;
		(*parameters)[i]->print(file_buffer);
	}
	file_buffer << ")";
}

/////////////////////////////////////////////////////////////////

template class Number_Ast<double>;
template class Number_Ast<int>;

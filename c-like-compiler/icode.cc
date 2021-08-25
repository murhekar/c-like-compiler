#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <list>
#include <map>

using namespace std;

#include "common-classes.hh"
#include "error-display.hh"
#include "icode.hh"
#include "reg-alloc.hh"
#include "symbol-table.hh"
#include "ast.hh"
#include "program.hh"

/****************************** Class Ics_Opd *****************************/

Register_Descriptor * Ics_Opd::get_reg()
{
    //TODO
}

/****************************** Class Mem_Addr_Opd *****************************/

Mem_Addr_Opd::Mem_Addr_Opd(Symbol_Table_Entry & se) 
{
    // Variable Name is passed as reference, that's why I am storing it in a variable
    string name = se.get_variable_name();
    Data_Type dt = se.get_data_type();
    int lineno = se.get_lineno();
    symbol_entry = new Symbol_Table_Entry(name, dt, lineno);
    symbol_entry->set_symbol_scope(se.get_symbol_scope());
    symbol_entry->set_start_offset(se.get_start_offset());
}

Mem_Addr_Opd & Mem_Addr_Opd::operator=(const Mem_Addr_Opd & rhs)
{
    delete symbol_entry;
    string name = rhs.symbol_entry->get_variable_name();
    Data_Type dt = rhs.symbol_entry->get_data_type();
    int lineno = rhs.symbol_entry->get_lineno();
    symbol_entry = new Symbol_Table_Entry(name, dt, lineno);
    symbol_entry->set_symbol_scope(rhs.symbol_entry->get_symbol_scope());
    return *this;
}

void Mem_Addr_Opd::print_ics_opd(ostream & file_buffer) 
{
    file_buffer << symbol_entry->get_variable_name();
}

void Mem_Addr_Opd::print_asm_opd(ostream & file_buffer) 
{
    Table_Scope symbol_scope = symbol_entry->get_symbol_scope();

    CHECK_INVARIANT(((symbol_scope == local) || (symbol_scope == global || symbol_scope == formal)), 
            "Wrong scope value");

    if (symbol_scope == local)
    {
        int offset = symbol_entry->get_start_offset();
        file_buffer << offset << "($fp)";
    }       
    else if (symbol_scope == formal)
    {
        int offset = symbol_entry->get_start_offset();
        file_buffer << offset << "($fp)";
    }
    else
    {
        file_buffer << symbol_entry->get_variable_name() + "_global";
    }
}

/****************************** Class Register_Addr_Opd *****************************/

// TODO: Need to check if this is allowed
Register_Addr_Opd::Register_Addr_Opd(Register_Descriptor * reg) 
{
    register_description = reg;
}

Register_Descriptor * Register_Addr_Opd::get_reg()    
{ 
    return register_description;
}

Register_Addr_Opd& Register_Addr_Opd::operator=(const Register_Addr_Opd& rhs)
{
    register_description = rhs.register_description;
    return *this;
}

void Register_Addr_Opd::print_ics_opd(ostream & file_buffer) 
{
    file_buffer << register_description->get_name();
}

void Register_Addr_Opd::print_asm_opd(ostream & file_buffer) 
{
    file_buffer << "$" << register_description->get_name();
}

/****************************** Class Const_Opd *****************************/

template <class DATA_TYPE>
Const_Opd<DATA_TYPE>::Const_Opd(DATA_TYPE n) 
{
    num = n;
}

template <class DATA_TYPE>
Const_Opd<DATA_TYPE> & Const_Opd<DATA_TYPE>::operator=(const Const_Opd<DATA_TYPE> & rhs)
{
    num = rhs.num;
}

template <class DATA_TYPE>
void Const_Opd<DATA_TYPE>::print_ics_opd(ostream & file_buffer) 
{
    file_buffer << num;
}

template <class DATA_TYPE>
void Const_Opd<DATA_TYPE>::print_asm_opd(ostream & file_buffer) 
{
    file_buffer << num;
}

/****************************** Class Icode_Stmt *****************************/

Instruction_Descriptor & Icode_Stmt::get_op()
{ 
    return op_desc; 
}

Ics_Opd * Icode_Stmt::get_opd1()
{
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method get_Opd1 not implemented");
}

Ics_Opd * Icode_Stmt::get_opd2()
{
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method get_Opd2 not implemented");
}

Ics_Opd * Icode_Stmt::get_result()
{
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method get_Result not implemented");
}

void Icode_Stmt::set_opd1(Ics_Opd * ics_opd)
{
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method set_Opd1 not implemented");
}

void Icode_Stmt::set_opd2(Ics_Opd * ics_opd)
{
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method set_Opd2 not implemented");
}

void Icode_Stmt::set_result(Ics_Opd * ics_opd)
{
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual methos set_Result not implemented");
}

/*************************** Class Formal_Store_Stmt *****************************/

Formal_Store_Stmt::Formal_Store_Stmt(Tgt_Op op, Ics_Opd* opd1, int off, string var_name)
{   // prints "sw opd, offset($sp)"
    CHECK_INVARIANT((machine_desc_object.spim_instruction_table[op] != NULL),
            "Instruction description in spim table cannot be null");

    op_desc = *(machine_desc_object.spim_instruction_table[op]);
    opd = opd1;
    offset = off;
    name = var_name;
}

void Formal_Store_Stmt::print_icode(ostream & file_buffer)
{
    string op_name = op_desc.get_name();
    file_buffer << "\t" << op_name << ":    \t";
    file_buffer << name << " <- ";
    opd->print_ics_opd(file_buffer);
    file_buffer << "\n";
}

void Formal_Store_Stmt::print_assembly(ostream & file_buffer)
{
    string op_name = op_desc.get_mnemonic();
    file_buffer << "\t" << op_name << " ";
    opd->print_asm_opd(file_buffer);
    file_buffer << ", " << offset <<"($sp)\n";
}

/*************************** Class Function_Call_Stmt *****************************/

Function_Call_Stmt::Function_Call_Stmt(string lab, int off)
{   
    label = lab;
    offset = off;
}

void Function_Call_Stmt::print_icode(ostream & file_buffer) {
    file_buffer << "\tcall " << label << endl;
}

void Function_Call_Stmt::print_assembly(ostream & file_buffer)
{
    file_buffer << "\tsub $sp, $sp, " << offset << "\n";
    file_buffer << "\tjal " << label << "\n";
    file_buffer << "\tadd $sp, $sp, " << offset << "\n";
}

/*************************** Class Move_IC_Stmt *****************************/

Move_IC_Stmt::Move_IC_Stmt(Tgt_Op op, Ics_Opd * o1, Ics_Opd * res)
{
    CHECK_INVARIANT((machine_desc_object.spim_instruction_table[op] != NULL),
            "Instruction description in spim table cannot be null");

    op_desc = *(machine_desc_object.spim_instruction_table[op]);
    opd1 = o1;   
    result = res; 
}

Ics_Opd * Move_IC_Stmt::get_opd1()          { return opd1; }
void Move_IC_Stmt::set_opd1(Ics_Opd * io)   { opd1 = io; }

Ics_Opd * Move_IC_Stmt::get_result()        { return result; }
void Move_IC_Stmt::set_result(Ics_Opd * io) { result = io; }

Move_IC_Stmt& Move_IC_Stmt::operator=(const Move_IC_Stmt& rhs)
{
    op_desc = rhs.op_desc;
    opd1 = rhs.opd1;
    result = rhs.result;

    return *this;
}

void Move_IC_Stmt::print_icode(ostream & file_buffer)
{
    CHECK_INVARIANT (opd1, "Opd1 cannot be NULL for a move IC Stmt");
    CHECK_INVARIANT (result, "Result cannot be NULL for a move IC Stmt");

    // std::cout << "Print icode for move" << endl;

    string operation_name = op_desc.get_name();

    Icode_Format ic_format = op_desc.get_ic_format();

    switch (ic_format)
    {
    case i_r_op_o1: 
            file_buffer << "\t" << operation_name << ":    \t";
            result->print_ics_opd(file_buffer);
            file_buffer << " <- ";
            opd1->print_ics_opd(file_buffer);
            file_buffer << "\n";

            break; 

    default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
                "Intermediate code format not supported");
        break;
    }
}

void Move_IC_Stmt::print_assembly(ostream & file_buffer)
{
    CHECK_INVARIANT (opd1, "Opd1 cannot be NULL for a move IC Stmt");
    CHECK_INVARIANT (result, "Result cannot be NULL for a move IC Stmt");
    string op_name = op_desc.get_mnemonic();

    Assembly_Format assem_format = op_desc.get_assembly_format();
    switch (assem_format)
    {
    case a_op_r_o1:

            if ((op_name == "lw" || op_name == "l.d") && typeid(*opd1) == typeid(Register_Addr_Opd)) {
                file_buffer << "\t" << op_name << " ";
                result->print_asm_opd(file_buffer);
                file_buffer << ", 0(";
                opd1->print_asm_opd(file_buffer);
                file_buffer << ")\n";
            } else {
                file_buffer << "\t" << op_name << " ";
                result->print_asm_opd(file_buffer);
                file_buffer << ", ";
                opd1->print_asm_opd(file_buffer);
                file_buffer << "\n";
            }

            break; 

    case a_op_o1_r:

            if ((op_name == "sw" || op_name == "s.d") && typeid(*result) == typeid(Register_Addr_Opd)) {
                file_buffer << "\t" << op_name << " ";
                opd1->print_asm_opd(file_buffer);
                file_buffer << ", 0(";
                result->print_asm_opd(file_buffer);
                file_buffer << ")\n";
            } else {
                file_buffer << "\t" << op_name << " ";
                opd1->print_asm_opd(file_buffer);
                file_buffer << ", ";
                result->print_asm_opd(file_buffer);
                file_buffer << "\n";
            }

            break; 

    default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "Intermediate code format not supported");
        break;
    }
}

/*************************** Class Compute_IC_Stmt *****************************/

Compute_IC_Stmt::Compute_IC_Stmt(Tgt_Op inst_op, Ics_Opd * res, Ics_Opd * o1, Ics_Opd * o2)
{
    CHECK_INVARIANT((machine_desc_object.spim_instruction_table[inst_op] != NULL),
            "Instruction description in spim table cannot be null");

    op_desc = *(machine_desc_object.spim_instruction_table[inst_op]);
    opd1 = o1;   
    opd2 = o2;
    result = res;
}

Compute_IC_Stmt& Compute_IC_Stmt::operator=(const Compute_IC_Stmt& rhs)
{
    op_desc = rhs.op_desc;
    opd1 = rhs.opd1;
    opd2 = rhs.opd2;
    result = rhs.result;

    return *this;
}

Ics_Opd * Compute_IC_Stmt::get_opd1() { return opd1; }
void Compute_IC_Stmt::set_opd1(Ics_Opd * io) { opd1 = io; }

Ics_Opd * Compute_IC_Stmt::get_opd2() { return opd2; }
void Compute_IC_Stmt::set_opd2(Ics_Opd * io) { opd2 = io; }

Ics_Opd * Compute_IC_Stmt::get_result() { return result; }
void Compute_IC_Stmt::set_result(Ics_Opd * io) { result = io; }

void Compute_IC_Stmt::print_icode(ostream & file_buffer)
{
    CHECK_INVARIANT (opd1, "Opd1 cannot be NULL for a compute IC Stmt");
    // CHECK_INVARIANT ((opd2 != NULL) || (op_desc.get_op() == uminus) || (op_desc.get_op() == uminus_d), "Opd2 cannot be NULL for a compute IC Stmt"); // for uminus
    CHECK_INVARIANT (result, "Result cannot be NULL for a compute IC Stmt");

    // std::cout << "Print icode for compute" << std::endl;

    string operation_name = op_desc.get_name();

    Icode_Format ic_format = op_desc.get_ic_format();

    switch (ic_format)
    {
    case i_r_o1_op_o2: 
            file_buffer << "\t" << operation_name << ":    \t";
            result->print_ics_opd(file_buffer);
            file_buffer << " <- ";
            opd1->print_ics_opd(file_buffer);
            file_buffer << " , ";
            opd2->print_ics_opd(file_buffer);
            file_buffer << "\n";

            break; 

    case i_r_op_o1: 
            file_buffer << "\t" << operation_name << ":    \t";
            result->print_ics_opd(file_buffer);
            file_buffer << " <- ";
            opd1->print_ics_opd(file_buffer);
            file_buffer << "\n";

            break; 

    case i_o1_op_o2:
            file_buffer << "\t" << operation_name << ":    \t";
            opd1->print_ics_opd(file_buffer);
            file_buffer << " <- ";
            opd2->print_ics_opd(file_buffer);
            file_buffer << "\n";

            break;

    default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
                "Intermediate code format not supported");
        break;
    }
}
void Compute_IC_Stmt::print_assembly(ostream & file_buffer)
{
    CHECK_INVARIANT (opd1, "Opd1 cannot be NULL for a compute IC Stmt");
    // CHECK_INVARIANT ((opd2 != NULL) || (op_desc.get_op() == uminus) || (op_desc.get_op() == uminus_d), "Opd2 cannot be NULL for a compute IC Stmt"); // UMINUS
    CHECK_INVARIANT (result, "Result cannot be NULL for a compute IC Stmt");

    string op_name = op_desc.get_mnemonic();

    Assembly_Format assem_format = op_desc.get_assembly_format();
    switch (assem_format)
    {
    case a_op_r_o1_o2: 
            file_buffer << "\t" << op_name << " ";
            result->print_asm_opd(file_buffer);
            file_buffer << ", ";
            opd1->print_asm_opd(file_buffer);
            file_buffer << ", ";
            opd2->print_asm_opd(file_buffer);
            file_buffer << "\n";

            break; 

    case a_op_o1_o2_r: 
            file_buffer << "\t" << op_name << " ";
            opd1->print_asm_opd(file_buffer);
            file_buffer << ", ";
            opd2->print_asm_opd(file_buffer);
            file_buffer << ", ";
            result->print_asm_opd(file_buffer);
            file_buffer << "\n";

            break; 

    case a_op_r_o1: 
            file_buffer << "\t" << op_name << " ";
            result->print_asm_opd(file_buffer);
            file_buffer << ", ";
            opd1->print_asm_opd(file_buffer);
            file_buffer << "\n";

            break; 

    case a_op_o1_r: 
            file_buffer << "\t" << op_name << " ";
            opd1->print_asm_opd(file_buffer);
            file_buffer << ", ";
            result->print_asm_opd(file_buffer);
            file_buffer << "\n";

            break; 
    
    case a_op_o1_o2:
            file_buffer << "\t" << op_name << " ";
            opd1->print_asm_opd(file_buffer);
            file_buffer << ", ";
            opd2->print_asm_opd(file_buffer);
            file_buffer << "\n";

            break;

    default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "Intermediate code format not supported");
        break;
    }
}

/*************************** Class Control_Flow_IC_Stmt *****************************/

Control_Flow_IC_Stmt::Control_Flow_IC_Stmt(Tgt_Op op, Ics_Opd * o1, Ics_Opd * o2, string label) 
{
    CHECK_INVARIANT((machine_desc_object.spim_instruction_table[op] != NULL),
            "Instruction description in spim table cannot be null");

    op_desc = *(machine_desc_object.spim_instruction_table[op]);
    opd1 = o1;   
    opd2 = o2;
    offset = label; // copying strings not arrays
}   

Control_Flow_IC_Stmt& Control_Flow_IC_Stmt::operator=(const Control_Flow_IC_Stmt& rhs)
{
    op_desc = rhs.op_desc;
    opd1 = rhs.opd1;
    opd2 = rhs.opd2;
    offset = rhs.offset;

    return *this;
}

Ics_Opd * Control_Flow_IC_Stmt::get_opd1() { return opd1; }
void Control_Flow_IC_Stmt::set_opd1(Ics_Opd * io) { opd1 = io; }

Ics_Opd * Control_Flow_IC_Stmt::get_opd2() { return opd2; }
void Control_Flow_IC_Stmt::set_opd2(Ics_Opd * io) { opd2 = io; }
    
string Control_Flow_IC_Stmt::get_Offset() { return offset; }
void Control_Flow_IC_Stmt::set_Offset(string label) { offset = label; }

void Control_Flow_IC_Stmt::print_icode(ostream & file_buffer) 
{
    // CHECK_INVARIANT (opd1, "Opd1 cannot be NULL for a control_flow IC Stmt"); // j stmt
    // CHECK_INVARIANT (opd2, "Opd2 cannot be NULL for a control_flow IC Stmt");

    // std::cout << "Print icode for control_flow" << std::endl;

    string operation_name = op_desc.get_name();
    
    Icode_Format ic_format = op_desc.get_ic_format();
    
    switch (ic_format)
    {
    case i_op_o1_o2_st: 
            file_buffer << "\t" << operation_name << ":    \t";
            opd1->print_ics_opd(file_buffer);
            file_buffer << " , ";
            opd2->print_ics_opd(file_buffer);
            file_buffer << " : goto " << offset << "\n";

            break; 

    case i_op_st:
            if(operation_name == "jal"){
                file_buffer << "\tcall " << offset << "\n";
            }
            else {
                file_buffer << "\tgoto " << offset << "\n";
            }

            break;

    case i_op: // return
            file_buffer << "\treturn \n";
            break;

    default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
                "Intermediate code format not supported");
        break;
    }

}

void Control_Flow_IC_Stmt::print_assembly(ostream & file_buffer) 
{
    // CHECK_INVARIANT (opd1, "opd1 cannot be NULL for a control_flow IC Stmt");
    // CHECK_INVARIANT (opd2, "opd2 cannot be NULL for a control_flow IC Stmt");

    string op_name = op_desc.get_mnemonic();

    Assembly_Format assem_format = op_desc.get_assembly_format();
    switch (assem_format)
    {
    case a_op_o1_o2_st: 
            file_buffer << "\t" << op_name << " ";
            opd1->print_asm_opd(file_buffer);
            file_buffer << ", ";
            opd2->print_asm_opd(file_buffer);
            file_buffer << ", " << offset << " \n";

            break; 

    case a_op_st:
            file_buffer << "\t" << op_name << " " << offset << "\n";        
            break;

    case a_op:
            file_buffer << "\t" << op_name << " " << offset << "\n";
            break;

    default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "Intermediate code format not supported");
        break;
    }
}

/******************************* Class Label_IC_Stmt ****************************/

Label_IC_Stmt::Label_IC_Stmt(Tgt_Op inst_op, Ics_Opd * o1, string off)
{
    CHECK_INVARIANT((machine_desc_object.spim_instruction_table[inst_op] != NULL),
            "Instruction description in spim table cannot be null");

    op_desc = *(machine_desc_object.spim_instruction_table[inst_op]);
    opd1 = o1;   
    offset = off; // copying strings not arrays
}
Label_IC_Stmt& Label_IC_Stmt::operator=(const Label_IC_Stmt& rhs)
{
    op_desc = rhs.op_desc;
    opd1 = rhs.opd1;
    offset = rhs.offset;

    return *this;
}

Ics_Opd * Label_IC_Stmt::get_opd1() { return opd1; }
void Label_IC_Stmt::set_opd1(Ics_Opd * io) { opd1 = io; }

string Label_IC_Stmt::get_offset() { return offset; }
void Label_IC_Stmt::set_offset(string label) { offset = label; }

void Label_IC_Stmt::print_icode(ostream & file_buffer) 
{
    // std::cout << "Print icode for label" << std::endl;
    string operation_name = op_desc.get_name();
    Icode_Format ic_format = op_desc.get_ic_format();

    switch (ic_format)
    {
    case i_op_st:
            if (operation_name == "syscall") {
                file_buffer << "\tsyscall\n";
            } else {
                file_buffer << "\n" << offset << ":    \t\n";
            } 
            break; 

    default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
                "Intermediate code format not supported");
        break;
    }
}

void Label_IC_Stmt::print_assembly(ostream & file_buffer) 
{
    string op_name = op_desc.get_mnemonic();

    Assembly_Format assem_format = op_desc.get_assembly_format();
    switch (assem_format)
    {
    case a_op_st: 
            if (op_name == "syscall") {
                file_buffer << "\tsyscall\n";
            } else {
                file_buffer << "\n" << offset << ":    \t\n";
            }
            break;
    
    default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "Intermediate code format not supported");
        break;
    }
}

/******************************* Class Code_For_Ast ****************************/

Code_For_Ast::Code_For_Ast()
{
    
}

Code_For_Ast::Code_For_Ast(list<Icode_Stmt *> & ic_l, Register_Descriptor * reg)
{
    ics_list = ic_l;
    result_register = reg;
}

void Code_For_Ast::append_ics(Icode_Stmt & ic_stmt)
{
    ics_list.push_back(&ic_stmt);
}

list<Icode_Stmt *> & Code_For_Ast::get_icode_list()  
{ 
    return ics_list;
}

Register_Descriptor * Code_For_Ast::get_reg()
{
    return result_register;
}

void Code_For_Ast::set_reg(Register_Descriptor * reg)
{
    result_register = reg;
}

Code_For_Ast& Code_For_Ast::operator=(const Code_For_Ast& rhs)
{
    ics_list = rhs.ics_list;
    result_register = rhs.result_register;
}

/************************ class Instruction_Descriptor ********************************/

Tgt_Op Instruction_Descriptor::get_op()                     { return inst_op; }
string Instruction_Descriptor::get_name()                       { return name; }
string Instruction_Descriptor::get_mnemonic()                   { return mnemonic; }
string Instruction_Descriptor::get_ic_symbol()                  { return ic_symbol; }
Icode_Format Instruction_Descriptor::get_ic_format()            { return ic_format; }
Assembly_Format Instruction_Descriptor::get_assembly_format()   { return assem_format; }

Instruction_Descriptor::Instruction_Descriptor (Tgt_Op op, string temp_name, string temp_mnemonic, 
                        string ic_sym, Icode_Format ic_form, Assembly_Format as_form)
{
    inst_op = op;
    name = temp_name; 
    mnemonic = temp_mnemonic;
    ic_symbol = ic_sym;
    ic_format = ic_form;
    assem_format = as_form;
}

Instruction_Descriptor::Instruction_Descriptor()
{
    inst_op = nop;
    name = "";
    mnemonic = "";
    ic_symbol = "";
    ic_format = i_nsy;
    assem_format = a_nsy;
}

template class Const_Opd<int>;
template class Const_Opd<double>;
template class Const_Opd<string>;


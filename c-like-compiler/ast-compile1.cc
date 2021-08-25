#include <iostream>
#include <fstream>
#include <typeinfo>

using namespace std;

#include "common-classes.hh"
#include "error-display.hh"
#include "user-options.hh"
#include "icode.hh"
#include "reg-alloc.hh"
#include "symbol-table.hh"
#include "ast.hh"
#include "procedure.hh"
#include "program.hh"

map<string, string> str_labels_map;

Code_For_Ast & Ast::create_store_stmt(Register_Descriptor * store_register)
{
    stringstream msg;
    msg << "No create_store_stmt() function for " << typeid(*this).name();
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

void Ast::print_assembly()
{
    stringstream msg;
    msg << "No print_assembly() function for " << typeid(*this).name();
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

void Ast::print_icode()
{
    stringstream msg;
    msg << "No print_icode() function for " << typeid(*this).name();
    CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

////////////////////////////////////////////////////////////////

Code_For_Ast & Assignment_Ast::compile()
{
    CHECK_INVARIANT((lhs != NULL), "Lhs cannot be null in Assignment_Ast");
    CHECK_INVARIANT((rhs != NULL), "Rhs cannot be null in Assignment_Ast");

    Code_For_Ast & load_stmt = rhs->compile();

    Register_Descriptor * load_register = load_stmt.get_reg();
    CHECK_INVARIANT(load_register, "Load register cannot be null in Assignment_Ast");
    load_register->set_use_for_expr_result();

    Code_For_Ast store_stmt = lhs->create_store_stmt(load_register);

    CHECK_INVARIANT((load_register != NULL), "Load register cannot be null in Assignment_Ast");
    load_register->reset_use_for_expr_result();

    // Store the statement in ic_list

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (load_stmt.get_icode_list().empty() == false)
        ic_list = load_stmt.get_icode_list();

    if (store_stmt.get_icode_list().empty() == false)
        ic_list.splice(ic_list.end(), store_stmt.get_icode_list());

    Code_For_Ast * assign_stmt;
    if (ic_list.empty() == false)
        assign_stmt = new Code_For_Ast(ic_list, load_register);

    return *assign_stmt;
}


/////////////////////////////////////////////////////////////////

Code_For_Ast & Name_Ast::compile()
{
    CHECK_INVARIANT(variable_symbol_entry, "Variable symbol entry cannot be null in Name_Ast");

    Ics_Opd * opd = new Mem_Addr_Opd(*variable_symbol_entry);

    Register_Descriptor * result_register = NULL;
    
    // Initialise result register appropriately
    // Take care that the result register is of proper type
    
    // TODO

    const Data_Type dt = get_data_type();

    if (dt == int_data_type) {
        result_register = machine_desc_object.get_new_register<gp_data>();
    } else if (dt == double_data_type) {
        result_register = machine_desc_object.get_new_register<float_reg>();
    }

    CHECK_INVARIANT((result_register != NULL), "Result register cannot be null in Name_Ast");

    Ics_Opd * register_opd = new Register_Addr_Opd(result_register);

    Icode_Stmt * load_stmt = NULL;
    
    // Initialise load_stmt appropriately
    // TODO

    if (dt == int_data_type) {
        load_stmt = new Move_IC_Stmt(load, opd, register_opd);
    } else if (dt == double_data_type) {
        load_stmt = new Move_IC_Stmt(load_d, opd, register_opd);
    }

    CHECK_INVARIANT((load_stmt != NULL), "Load statement cannot be null in Name_Ast");

    list<Icode_Stmt *> ic_list;
    ic_list.push_back(load_stmt);

    Code_For_Ast & load_code = *new Code_For_Ast(ic_list, result_register);

    return load_code;
}

Code_For_Ast & Name_Ast::create_store_stmt(Register_Descriptor * store_register)
{
    CHECK_INVARIANT((store_register != NULL), "Store register cannot be null in Name_Ast");
    CHECK_INVARIANT(variable_symbol_entry, "Variable symbol entry cannot be null in Name_Ast");

    Ics_Opd * register_opd = new Register_Addr_Opd(store_register);
    Ics_Opd * opd = new Mem_Addr_Opd(*variable_symbol_entry);

    Icode_Stmt * store_stmt = NULL;
    
    // Initialise store_stmt appropriately
    // TODO

    const Data_Type dt = get_data_type();

    if (dt == int_data_type) {
        store_stmt = new Move_IC_Stmt(store, register_opd, opd);
    } else if (dt == double_data_type) {
        store_stmt = new Move_IC_Stmt(store_d, register_opd, opd);
    }

    CHECK_INVARIANT((store_stmt != NULL), "Store statement cannot be null in Name_Ast");

    // TODO -- Uncomment and resolve LRA related errors
    // if (command_options.is_do_lra_selected() == false)
    // {
    //     variable_symbol_entry->free_register(store_register);
    // }
    // else
    // {
    //     variable_symbol_entry->update_register(store_register);
    //     store_register->reset_use_for_expr_result();
    // }

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;
    ic_list.push_back(store_stmt);

    Code_For_Ast & name_code = *new Code_For_Ast(ic_list, store_register);

    return name_code;
}


///////////////////////////////////////////////////////////////////////////////

template <class DATA_TYPE>
Code_For_Ast & Number_Ast<DATA_TYPE>::compile()
{
    Const_Opd<DATA_TYPE>* opd1 = new Const_Opd<DATA_TYPE>(constant);

    const Data_Type dt = get_data_type();

    Register_Descriptor * result_register = NULL;
    if (dt == int_data_type) {
        result_register = machine_desc_object.get_new_register<gp_data>();
    } else if (dt == double_data_type) {
        result_register = machine_desc_object.get_new_register<float_reg>();
    }

    CHECK_INVARIANT((result_register != NULL), "Result register cannot be null in Number_Ast");

    Register_Addr_Opd* register_opd = new Register_Addr_Opd(result_register);

    Move_IC_Stmt* load_stmt = NULL;
    if (get_data_type() == int_data_type) {
        load_stmt = new Move_IC_Stmt(imm_load, opd1, register_opd);
    } else if (get_data_type() == double_data_type) {
        load_stmt = new Move_IC_Stmt(imm_load_d, opd1, register_opd);
    }

    CHECK_INVARIANT((load_stmt != NULL), "Load statement cannot be null in Number_Ast");
    
    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;
    ic_list.push_back(load_stmt);
    
    Code_For_Ast* cfa_load_stmt;
    cfa_load_stmt = new Code_For_Ast(ic_list, result_register);

    return *cfa_load_stmt;
}

///////////////////////////////////////////////////////////////////////////////

Code_For_Ast & Relational_Expr_Ast::compile()
{
    CHECK_INVARIANT((lhs_condition != NULL), "LHS cannot be null in Relational_Expr_Ast");
    CHECK_INVARIANT((rhs_condition != NULL), "RHS cannot be null in Relational_Expr_Ast");
    
    Code_For_Ast &left = lhs_condition->compile();
    Register_Descriptor* left_place = left.get_reg();
    Register_Addr_Opd* o1 = new Register_Addr_Opd(left_place);
    CHECK_INVARIANT(left_place, "LHS Register cannot be null in Relational_Expr_Ast");

    Code_For_Ast &right = rhs_condition->compile();
    Register_Descriptor* right_place = right.get_reg();
    Register_Addr_Opd* o2 = new Register_Addr_Opd(right_place);
    CHECK_INVARIANT(right_place, "RHS Register cannot be null in Relational_Expr_Ast");

    Register_Addr_Opd* result;
    result = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());    
    
    left_place->reset_use_for_expr_result();
    right_place->reset_use_for_expr_result();

    Compute_IC_Stmt* rel_stmt;
    
    switch(rel_op) 
    {
        case less_equalto:
                rel_stmt = new Compute_IC_Stmt(sle, result, o1, o2);
                break;
        case less_than:
                rel_stmt = new Compute_IC_Stmt(slt, result, o1, o2);
                break;
        case greater_than:
                rel_stmt = new Compute_IC_Stmt(sgt, result, o1, o2);
                break;
        case greater_equalto:
                rel_stmt = new Compute_IC_Stmt(sge, result, o1, o2);
                break;
        case equalto:
                rel_stmt = new Compute_IC_Stmt(seq, result, o1, o2);
                break;
        case not_equalto:
                rel_stmt = new Compute_IC_Stmt(sne, result, o1, o2);
                break;
    }

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (!left.get_icode_list().empty())
        ic_list = left.get_icode_list();

    if (!right.get_icode_list().empty())
        ic_list.splice(ic_list.end(), right.get_icode_list());

    CHECK_INVARIANT((rel_stmt != NULL), "Relational Expression statement cannot be null in Relational_Expr_Ast");

    ic_list.push_back(rel_stmt);

    Code_For_Ast * cfa_rel_stmt;
    cfa_rel_stmt = new Code_For_Ast(ic_list, result->get_reg());

    return *cfa_rel_stmt;
}

//////////////////////////////////////////////////////////////////////

Code_For_Ast & Boolean_Expr_Ast::compile()
{
    CHECK_INVARIANT((lhs_op != NULL || bool_op == boolean_not), "LHS cannot be null in Boolean_Expr_Ast"); // NOT
    CHECK_INVARIANT((rhs_op != NULL), "RHS cannot be null in Boolean_Expr_Ast");
    
    Register_Addr_Opd* o1;
    Register_Descriptor* left_place;
    Move_IC_Stmt* move_one_stmt;
    list<Icode_Stmt *> & left_ic_list = *new list<Icode_Stmt *>;

    if(bool_op == boolean_not)
    {
        Const_Opd<int>* val_one = new Const_Opd<int>(1);
        o1 = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());
        left_place = o1->get_reg();
        move_one_stmt = new Move_IC_Stmt(imm_load, val_one, o1);
    }
    else
    {
        Code_For_Ast &left = lhs_op->compile();
        left_place = left.get_reg();
        o1 = new Register_Addr_Opd(left_place);
        CHECK_INVARIANT(left_place, "LHS Register cannot be null in Boolean_Expr_Ast");
        if (!left.get_icode_list().empty())
            left_ic_list = left.get_icode_list();
    }

    Code_For_Ast &right = rhs_op->compile();
    Register_Descriptor* right_place = right.get_reg();
    Register_Addr_Opd* o2 = new Register_Addr_Opd(right_place);
    CHECK_INVARIANT(right_place, "RHS Register cannot be null in Boolean_Expr_Ast");

    Register_Addr_Opd* result = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());
    
    left_place->reset_use_for_expr_result();
    right_place->reset_use_for_expr_result();

    Compute_IC_Stmt* bool_stmt;
    
    switch(bool_op) 
    {
        case boolean_and:
                bool_stmt = new Compute_IC_Stmt(and_t, result, o1, o2);
                break;
        case boolean_or:
                bool_stmt = new Compute_IC_Stmt(or_t, result, o1, o2);
                break;
        case boolean_not:
                bool_stmt = new Compute_IC_Stmt(not_t, result, o2, o1);
                break;
    }

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if(bool_op == boolean_not)
    {
        ic_list.push_back(move_one_stmt);
    }
    else
    {
        ic_list = left_ic_list;
    }
    
    if (!right.get_icode_list().empty())
        ic_list.splice(ic_list.end(), right.get_icode_list());
    
    CHECK_INVARIANT((bool_stmt != NULL), "Boolean Expression statement cannot be null in Boolean_Expr_Ast");

    ic_list.push_back(bool_stmt);

    Code_For_Ast * cfa_bool_stmt;
    cfa_bool_stmt = new Code_For_Ast(ic_list, result->get_reg());

    return *cfa_bool_stmt;
}
///////////////////////////////////////////////////////////////////////

Code_For_Ast & Selection_Statement_Ast::compile()
{
    CHECK_INVARIANT((cond != NULL), "cond cannot be null in Selection_Statement_Ast"); 
    CHECK_INVARIANT((then_part != NULL), "then_part cannot be null in Selection_Statement_Ast");
    CHECK_INVARIANT((else_part != NULL), "else_part cannot be null in Selection_Statement_Ast");
    
    Code_For_Ast &condn = cond->compile();

    Code_For_Ast &thenp = then_part->compile();

    Code_For_Ast &elsep = else_part->compile();

    Register_Addr_Opd* op = new Register_Addr_Opd(condn.get_reg());
    Register_Descriptor* zeroreg = new Register_Descriptor(zero, "zero", int_num, fixed_reg);
    Register_Addr_Opd* zero = new Register_Addr_Opd(zeroreg);    
    string label_1 = get_new_label(); // k
    string label_2 = get_new_label(); // k+1
    Control_Flow_IC_Stmt* beq_stmt = new Control_Flow_IC_Stmt(beq, op, zero, label_1);
    Control_Flow_IC_Stmt* goto_stmt = new Control_Flow_IC_Stmt(j, NULL, NULL, label_2);
    Label_IC_Stmt* label_stmt_1 = new Label_IC_Stmt(label, NULL, label_1);
    Label_IC_Stmt* label_stmt_2 = new Label_IC_Stmt(label, NULL, label_2);

    (op->get_reg())->reset_use_for_expr_result();

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if(!condn.get_icode_list().empty())
    {
        ic_list = condn.get_icode_list();
    }
    ic_list.push_back(beq_stmt);

    if( !thenp.get_icode_list().empty())
    {
        ic_list.splice(ic_list.end(), thenp.get_icode_list());
    }

    ic_list.push_back(goto_stmt);
    ic_list.push_back(label_stmt_1);
    if(!elsep.get_icode_list().empty())
    {
        ic_list.splice(ic_list.end(), elsep.get_icode_list());
    }
    ic_list.push_back(label_stmt_2);

    Code_For_Ast * cfa_sel_stmt;
    cfa_sel_stmt = new Code_For_Ast(ic_list, NULL);
    
    return *cfa_sel_stmt;
}

///////////////////////////////////////////////////////////////////////////////////////////

Code_For_Ast & Iteration_Statement_Ast::compile()
{
    CHECK_INVARIANT((cond != NULL), "cond cannot be null in Iteration_Statement_Ast"); 
    CHECK_INVARIANT((body != NULL), "body cannot be null in Iteration_Statement_Ast");
    
    string label_1 = get_new_label(); // k
    string label_2 = get_new_label(); // k+1
    
    Code_For_Ast &condn = cond->compile();

    Code_For_Ast &bodyp = body->compile();

    Register_Addr_Opd* op = new Register_Addr_Opd(condn.get_reg());
    Register_Descriptor* zeroreg = new Register_Descriptor(zero, "zero", int_num, fixed_reg);
    Register_Addr_Opd* zero = new Register_Addr_Opd(zeroreg);
    // string label_1 = get_new_label(); // k
    // string label_2 = get_new_label(); // k+1
    Control_Flow_IC_Stmt* bne_stmt = new Control_Flow_IC_Stmt(bne, op, zero, label_1);
    Control_Flow_IC_Stmt* goto_stmt = new Control_Flow_IC_Stmt(j, NULL, NULL, label_2);
    Label_IC_Stmt* label_stmt_1 = new Label_IC_Stmt(label, NULL, label_1);
    Label_IC_Stmt* label_stmt_2 = new Label_IC_Stmt(label, NULL, label_2);

    (op->get_reg())->reset_use_for_expr_result();

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (!is_do_form) {
        ic_list.push_back(goto_stmt);
    }
    ic_list.push_back(label_stmt_1);

    if(!bodyp.get_icode_list().empty())
    {
        ic_list.splice(ic_list.end(), bodyp.get_icode_list());
    }

    ic_list.push_back(label_stmt_2);
    if(!condn.get_icode_list().empty())
    {
        ic_list.splice(ic_list.end(), condn.get_icode_list());
    }
    ic_list.push_back(bne_stmt);

    Code_For_Ast * cfa_iter_stmt;
    cfa_iter_stmt = new Code_For_Ast(ic_list, NULL);

    return *cfa_iter_stmt;
}

///////////////////////////////////////////////////////////////////////////////////////////

Code_For_Ast & Plus_Ast::compile()
{
    CHECK_INVARIANT((lhs != NULL), "lhs cannot be null in Plus_Ast");
    CHECK_INVARIANT((rhs != NULL), "rhs cannot be null in Plus_Ast");
    
    Code_For_Ast &left = lhs->compile();
    Register_Descriptor* left_place = left.get_reg();
    Register_Addr_Opd* o1 = new Register_Addr_Opd(left_place);
    CHECK_INVARIANT(left_place, "LHS Register cannot be null in Plus_Ast");

    Code_For_Ast &right = rhs->compile();
    Register_Descriptor* right_place = right.get_reg();
    Register_Addr_Opd* o2 = new Register_Addr_Opd(right_place);
    CHECK_INVARIANT(right_place, "RHS Register cannot be null in Plus_Ast");

    const Data_Type dt = get_data_type();
    Register_Addr_Opd* result;

    if (dt == int_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());    
    }
    else if (dt == double_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<float_reg>());
    }

    left_place->reset_use_for_expr_result();
    right_place->reset_use_for_expr_result();

    Compute_IC_Stmt* plus_stmt;
    if (dt == int_data_type) 
    {
        plus_stmt = new Compute_IC_Stmt(add, result, o1, o2);
    } 
    else if (dt == double_data_type) 
    {
        plus_stmt = new Compute_IC_Stmt(add_d, result, o1, o2);
    }

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (!left.get_icode_list().empty())
        ic_list = left.get_icode_list();

    if (!right.get_icode_list().empty())
        ic_list.splice(ic_list.end(), right.get_icode_list());

    CHECK_INVARIANT((plus_stmt != NULL), "Arith Expression statement cannot be null in Arith_Expr_Ast");

    ic_list.push_back(plus_stmt);

    Code_For_Ast * cfa_plus_stmt;
    cfa_plus_stmt = new Code_For_Ast(ic_list, result->get_reg());

    return *cfa_plus_stmt;
}

/////////////////////////////////////////////////////////////////

Code_For_Ast & Minus_Ast::compile()
{
    CHECK_INVARIANT((lhs != NULL), "lhs cannot be null in Minus_Ast");
    CHECK_INVARIANT((rhs != NULL), "rhs cannot be null in Minus_Ast");
    
    Code_For_Ast &left = lhs->compile();
    Register_Descriptor* left_place = left.get_reg();
    Register_Addr_Opd* o1 = new Register_Addr_Opd(left_place);
    CHECK_INVARIANT(left_place, "LHS Register cannot be null in Minus_Ast");

    Code_For_Ast &right = rhs->compile();
    Register_Descriptor* right_place = right.get_reg();
    Register_Addr_Opd* o2 = new Register_Addr_Opd(right_place);
    CHECK_INVARIANT(right_place, "RHS Register cannot be null in Minus_Ast");

    const Data_Type dt = get_data_type();
    Register_Addr_Opd* result;

    if (dt == int_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());    
    }
    else if (dt == double_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<float_reg>());
    }

    left_place->reset_use_for_expr_result();
    right_place->reset_use_for_expr_result();

    Compute_IC_Stmt* minus_stmt;
    if (dt == int_data_type) 
    {
        minus_stmt = new Compute_IC_Stmt(sub, result, o1, o2);
    } 
    else if (dt == double_data_type) 
    {
        minus_stmt = new Compute_IC_Stmt(sub_d, result, o1, o2);
    }

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (!left.get_icode_list().empty())
        ic_list = left.get_icode_list();

    if (!right.get_icode_list().empty())
        ic_list.splice(ic_list.end(), right.get_icode_list());

    CHECK_INVARIANT((minus_stmt != NULL), "Arith Expression statement cannot be null in Arith_Expr_Ast");

    ic_list.push_back(minus_stmt);

    Code_For_Ast * cfa_minus_stmt;
    cfa_minus_stmt = new Code_For_Ast(ic_list, result->get_reg());

    return *cfa_minus_stmt;
}

//////////////////////////////////////////////////////////////////

Code_For_Ast & Mult_Ast::compile()
{
    CHECK_INVARIANT((lhs != NULL), "lhs cannot be null in Mult_Ast");
    CHECK_INVARIANT((rhs != NULL), "rhs cannot be null in Mult_Ast");

    Code_For_Ast &left = lhs->compile();
    Register_Descriptor* left_place = left.get_reg();
    Register_Addr_Opd* o1 = new Register_Addr_Opd(left_place);
    CHECK_INVARIANT(left_place, "LHS Register cannot be null in Mult_Ast");

    Code_For_Ast &right = rhs->compile();
    Register_Descriptor* right_place = right.get_reg();
    Register_Addr_Opd* o2 = new Register_Addr_Opd(right_place);
    CHECK_INVARIANT(right_place, "RHS Register cannot be null in Mult_Ast");

    const Data_Type dt = get_data_type();
    Register_Addr_Opd* result;

    if (dt == int_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());    
    }
    else if (dt == double_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<float_reg>());
    }

    left_place->reset_use_for_expr_result();
    right_place->reset_use_for_expr_result();

    Compute_IC_Stmt* mult_stmt;
    if (dt == int_data_type) 
    {
        mult_stmt = new Compute_IC_Stmt(mult, result, o1, o2);
    } 
    else if (dt == double_data_type) 
    {
        mult_stmt = new Compute_IC_Stmt(mult_d, result, o1, o2);
    }

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (!left.get_icode_list().empty())
        ic_list = left.get_icode_list();

    if (!right.get_icode_list().empty())
        ic_list.splice(ic_list.end(), right.get_icode_list());

    CHECK_INVARIANT((mult_stmt != NULL), "Arith Expression statement cannot be null in Arith_Expr_Ast");

    ic_list.push_back(mult_stmt);   

    Code_For_Ast * cfa_mult_stmt;
    cfa_mult_stmt = new Code_For_Ast(ic_list, result->get_reg());

    return *cfa_mult_stmt;
}

////////////////////////////////////////////////////////////////////

Code_For_Ast & Conditional_Operator_Ast::compile()
{
    CHECK_INVARIANT((lhs != NULL), "lhs cannot be null in Conditional_Operator_Ast");
    CHECK_INVARIANT((rhs != NULL), "rhs cannot be null in Conditional_Operator_Ast");
    CHECK_INVARIANT((cond != NULL), "cond cannot be null in Conditional_Operator_Ast");

    Code_For_Ast &condn = cond->compile();

    Code_For_Ast &left = lhs->compile();
    Register_Descriptor* left_place = left.get_reg();
    Register_Addr_Opd* o1 = new Register_Addr_Opd(left_place);
    CHECK_INVARIANT(left_place, "LHS Register cannot be null in Conditional_Operator_Ast");

    Code_For_Ast &right = rhs->compile();
    Register_Descriptor* right_place = right.get_reg();
    Register_Addr_Opd* o2 = new Register_Addr_Opd(right_place);
    CHECK_INVARIANT(right_place, "RHS Register cannot be null in Conditional_Operator_Ast");
    
    Register_Addr_Opd* op = new Register_Addr_Opd(condn.get_reg());
    Register_Descriptor* zeroreg = new Register_Descriptor(zero, "zero", int_num, fixed_reg);
    Register_Addr_Opd* zero = new Register_Addr_Opd(zeroreg);    
    string label_1 = get_new_label(); // k
    string label_2 = get_new_label(); // k+1
    Control_Flow_IC_Stmt* beq_stmt = new Control_Flow_IC_Stmt(beq, op, zero, label_1);
    Control_Flow_IC_Stmt* goto_stmt = new Control_Flow_IC_Stmt(j, NULL, NULL, label_2);
    Label_IC_Stmt* label_stmt_1 = new Label_IC_Stmt(label, NULL, label_1);
    Label_IC_Stmt* label_stmt_2 = new Label_IC_Stmt(label, NULL, label_2);

    const Data_Type dt = get_data_type();
    Register_Addr_Opd* result;

    if (dt == int_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());    
    }
    else if (dt == double_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<float_reg>());
    }

    left_place->reset_use_for_expr_result();
    right_place->reset_use_for_expr_result();

    (op->get_reg())->reset_use_for_expr_result();

    Compute_IC_Stmt* or_stmt_1;
    Compute_IC_Stmt* or_stmt_2;
    or_stmt_1 = new Compute_IC_Stmt(or_t, result, o1, zero);
    or_stmt_2 = new Compute_IC_Stmt(or_t, result, o2, zero);

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if(!condn.get_icode_list().empty())
    {
        ic_list = condn.get_icode_list();
    }
    ic_list.push_back(beq_stmt);

    if( !left.get_icode_list().empty())
    {
        ic_list.splice(ic_list.end(), left.get_icode_list());
    }
    ic_list.push_back(or_stmt_1);
    ic_list.push_back(goto_stmt);

    ic_list.push_back(label_stmt_1);
    if(!right.get_icode_list().empty())
    {
        ic_list.splice(ic_list.end(), right.get_icode_list());
    }
    ic_list.push_back(or_stmt_2);

    ic_list.push_back(label_stmt_2);

    Code_For_Ast * cfa_sel_stmt;
    cfa_sel_stmt = new Code_For_Ast(ic_list, result->get_reg());

    return *cfa_sel_stmt;
}


////////////////////////////////////////////////////////////////////

Code_For_Ast & Divide_Ast::compile()
{
    CHECK_INVARIANT((lhs != NULL), "lhs cannot be null in Divide_Ast");
    CHECK_INVARIANT((rhs != NULL), "rhs cannot be null in Divide_Ast");
    
    // std::cout << "in compile of divd" << std::endl;

    Code_For_Ast &left = lhs->compile();
    Register_Descriptor* left_place = left.get_reg();
    Register_Addr_Opd* o1 = new Register_Addr_Opd(left_place);
    CHECK_INVARIANT(left_place, "LHS Register cannot be null in Divide_Ast");

    Code_For_Ast &right = rhs->compile();
    Register_Descriptor* right_place = right.get_reg();
    Register_Addr_Opd* o2 = new Register_Addr_Opd(right_place);
    CHECK_INVARIANT(right_place, "RHS Register cannot be null in Divide_Ast");

    const Data_Type dt = get_data_type();
    Register_Addr_Opd* result;

    if (dt == int_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());    
    }
    else if (dt == double_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<float_reg>());
    }

    left_place->reset_use_for_expr_result();
    right_place->reset_use_for_expr_result();

    Compute_IC_Stmt* div_stmt;
    if (dt == int_data_type) 
    {
        div_stmt = new Compute_IC_Stmt(divd, result, o1, o2);
    } 
    else if (dt == double_data_type) 
    {
        div_stmt = new Compute_IC_Stmt(div_d, result, o1, o2);
    }

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (!left.get_icode_list().empty())
        ic_list = left.get_icode_list();

    if (!right.get_icode_list().empty())
        ic_list.splice(ic_list.end(), right.get_icode_list());

    CHECK_INVARIANT((div_stmt != NULL), "Arith Expression statement cannot be null in Arith_Expr_Ast");

    ic_list.push_back(div_stmt);

    Code_For_Ast * cfa_div_stmt;
    cfa_div_stmt = new Code_For_Ast(ic_list, result->get_reg());

    return *cfa_div_stmt;
}


//////////////////////////////////////////////////////////////////////

Code_For_Ast & UMinus_Ast::compile()
{
    CHECK_INVARIANT((lhs != NULL), "lhs cannot be null in UMinus_Ast");

    Code_For_Ast &left = lhs->compile();
    Register_Descriptor* left_place = left.get_reg();
    Register_Addr_Opd* o1 = new Register_Addr_Opd(left_place);
    CHECK_INVARIANT(left_place, "LHS Register cannot be null in UMinus_Ast");

    const Data_Type dt = get_data_type();
    Register_Addr_Opd* result;

    if (dt == int_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<gp_data>());    
    }
    else if (dt == double_data_type) 
    {
        result = new Register_Addr_Opd(machine_desc_object.get_new_register<float_reg>());
    }

    left_place->reset_use_for_expr_result();
    
    Compute_IC_Stmt* uminus_stmt;
    if (dt == int_data_type) 
    {
        uminus_stmt = new Compute_IC_Stmt(uminus, result, o1, NULL);
    } 
    else if (dt == double_data_type) 
    {
        uminus_stmt = new Compute_IC_Stmt(uminus_d, result, o1, NULL);
    }

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (!left.get_icode_list().empty())
        ic_list = left.get_icode_list();

    CHECK_INVARIANT((uminus_stmt != NULL), "Arith Expression statement cannot be null in Arith_Expr_Ast");

    ic_list.push_back(uminus_stmt);

    Code_For_Ast * cfa_uminus_stmt;
    cfa_uminus_stmt = new Code_For_Ast(ic_list, result->get_reg());

    return *cfa_uminus_stmt;
}

//////////////////////////////////////////////////////////////////////////////

Code_For_Ast & Sequence_Ast::compile()
{
    sa_icode_list = *new list<Icode_Stmt *>;
    Register_Descriptor* reg;
    for (list<Ast*> :: iterator it = statement_list.begin(); it != statement_list.end(); ++it) {
        Code_For_Ast & stmt = (*it)->compile();
        sa_icode_list.splice(sa_icode_list.end(), stmt.get_icode_list());
    }
    Code_For_Ast * seqast;
    seqast = new Code_For_Ast(sa_icode_list, NULL);
    return *seqast;
}

void Sequence_Ast::print_assembly(ostream & file_buffer)
{
    for (list<Icode_Stmt*> :: iterator it = sa_icode_list.begin(); it != sa_icode_list.end(); ++it) {
        (*it)->print_assembly(file_buffer);
    }
}

void Sequence_Ast::print_icode(ostream & file_buffer)
{
    for (list<Icode_Stmt*> :: iterator it = sa_icode_list.begin(); it != sa_icode_list.end(); ++it) {
        (*it)->print_icode(file_buffer);
    }
}

//////////////////////////////////////////////////////////////////////////////

Code_For_Ast & String_Ast::compile() {
    string_label = get_new_string_label();
    str_labels_map[string_label] = const_string;
}

//////////////////////////////////////////////////////////////////////////////

Code_For_Ast & Return_Ast::compile() {

}

//////////////////////////////////////////////////////////////////////////////

Code_For_Ast & Print_Ast::compile() {
    CHECK_INVARIANT((print_ast != NULL), "Cannot have null argument in print");
    
    Code_For_Ast &param = print_ast->compile();

    const Data_Type print_dt = print_ast->get_data_type();

    if (print_dt != string_data_type) {
        CHECK_INVARIANT((param != NULL), "Parameter Code cannot be null");
    }

    Register_Descriptor* sp_reg = machine_desc_object.spim_register_table[sp];
    Register_Descriptor* v0_reg = machine_desc_object.spim_register_table[v0];
    Register_Descriptor* a0_reg = machine_desc_object.spim_register_table[a0];
    Register_Descriptor* f12_reg = machine_desc_object.spim_register_table[f12];

    Const_Opd<int>* opd2_4 = new Const_Opd<int>(-4);
    Const_Opd<int>* opd2_8 = new Const_Opd<int>(-8);

    Compute_IC_Stmt* push_stmt_1 = new Compute_IC_Stmt(imm_add, sp_reg, sp_reg, opd2_4);
    Compute_IC_Stmt* push_stmt_2 = new Compute_IC_Stmt(imm_add, sp_reg, sp_reg, opd2_4);
    Compute_IC_Stmt* push_stmt_3 = new Compute_IC_Stmt(imm_add, sp_reg, sp_reg, opd2_8);

    Move_IC_Stmt* v0_sw_stmt = new Move_IC_Stmt(store, v0_reg, sp_reg);
    Move_IC_Stmt* a0_sw_stmt = new Move_IC_Stmt(store, a0_reg, sp_reg);
    Move_IC_Stmt* f12_sw_stmt = new Move_IC_Stmt(store_d, f12_reg, sp_reg);

    Move_IC_Stmt* la_stmt;
    Move_IC_Stmt* load_stmt;

    if (print_dt == string_data_type) {
        Const_Opd<string> str_opd = new Const_Opd<string>(print_ast->get_string_label());
        la_stmt = new Move_IC_Stmt(la, str_opd, a0_reg);

        Const_Opd<int>* opd_4 = new Const_Opd<int>(4);
        load_stmt = new Move_IC_Stmt(imm_load, opd_4, v0_reg);
    } else if (print_dt == int_data_type) {
        Register_Descriptor* param_reg = param.get_reg();
        Register_Addr_Opd* o1 = new Register_Addr_Opd(param_reg);
        CHECK_INVARIANT(param_reg, "Parameter Register cannot be null in Print_Ast");
        la_stmt = new Move_IC_Stmt(move, o1, a0_reg);
        param_reg->reset_use_for_expr_result();

        Const_Opd<int>* opd_1 = new Const_Opd<int>(1);
        load_stmt = new Move_IC_Stmt(imm_load, opd_1, v0_reg);
    } else if (print_dt == double_data_type) {
        Register_Descriptor* param_reg = param.get_reg();
        Register_Addr_Opd* o1 = new Register_Addr_Opd(param_reg);
        CHECK_INVARIANT(param_reg, "Parameter Register cannot be null in Print_Ast");
        la_stmt = new Move_IC_Stmt(move_d, o1, a0_reg);
        param_reg->reset_use_for_expr_result();

        Const_Opd<int>* opd_2 = new Const_Opd<int>(2);
        load_stmt = new Move_IC_Stmt(imm_load, opd_2, v0_reg);
    }

    Label_IC_Stmt* syscall_stmt = new Label_IC_Stmt(syscall, NULL, "");

    Const_Opd<int>* opd2_41 = new Const_Opd<int>(4);
    Const_Opd<int>* opd2_81 = new Const_Opd<int>(8);

    Compute_IC_Stmt* pop_stmt_1 = new Compute_IC_Stmt(imm_add, sp_reg, sp_reg, opd2_41);
    Compute_IC_Stmt* pop_stmt_2 = new Compute_IC_Stmt(imm_add, sp_reg, sp_reg, opd2_41);
    Compute_IC_Stmt* pop_stmt_3 = new Compute_IC_Stmt(imm_add, sp_reg, sp_reg, opd2_81);

    Move_IC_Stmt* v0_lw_stmt = new Move_IC_Stmt(load, sp_reg, v0_reg);
    Move_IC_Stmt* a0_lw_stmt = new Move_IC_Stmt(load, sp_reg, a0_reg);
    Move_IC_Stmt* f12_lw_stmt = new Move_IC_Stmt(load_d, sp_reg, f12_reg);

    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    if (print_dt != string_data_type) {
        if (!param.get_icode_list().empty())
            ic_list.splice(ic_list.end(), param.get_icode_list());
    }

    ic_list.push_back(push_stmt_1);
    ic_list.push_back(v0_sw_stmt);
    ic_list.push_back(push_stmt_2);
    ic_list.push_back(a0_sw_stmt);
    ic_list.push_back(push_stmt_3);
    ic_list.push_back(f12_sw_stmt);

    ic_list.push_back(la_stmt);
    ic_list.push_back(load_stmt);
    ic_list.push_back(syscall_stmt);

    ic_list.push_back(f12_lw_stmt);
    ic_list.push_back(pop_stmt_3);
    ic_list.push_back(a0_lw_stmt);
    ic_list.push_back(pop_stmt_2);
    ic_list.push_back(v0_lw_stmt);
    ic_list.push_back(pop_stmt_1);

    Code_For_Ast * cfa_print_stmt;
    cfa_print_stmt = new Code_For_Ast(ic_list, NULL);

    return *cfa_print_stmt;
}

//////////////////////////////////////////////////////////////////////////////

Code_For_Ast & Function_Call_Ast::compile() {

}

//////////////////////////////////////////////////////////////////////////////

template class Number_Ast<double>;
template class Number_Ast<int>;

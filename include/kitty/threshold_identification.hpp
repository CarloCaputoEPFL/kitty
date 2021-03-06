/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification
  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "isop.hpp"
#include "properties.hpp"
#include "implicant.hpp"

namespace kitty
{

/*! \brief Threshold logic function identification
  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as
  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T
  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].
  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of tt if it is a TF.
             The linear form has tt.num_vars() weight values and the threshold value
             in the end.
  \return true if tt is a TF; false if tt is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  TT mytt = tt;
  int num_vars = tt.num_vars();
  std::vector<bool> var_inv( num_vars, false ); //vector if the inverted variables

  /*check unteness for each variable and in case flip xi*/
  for ( int i = 0u; i < num_vars; ++i )
  {
    //check of the function

    // auto num_vars= tt.num_vars();
    bool su = false, giu = false;

    auto cof0 = cofactor0( tt, i );
    auto cof1 = cofactor1( tt, i );

    uint32_t Num = tt.num_bits();

    for ( auto j = 0u; j < Num; ++j )
    {
      if ( get_bit( cof1, j ) > get_bit( cof0, j ) )
        su = true;
      if ( get_bit( cof1, j ) < get_bit( cof0, j ) )
        giu = true;
    }
    //binate
    if ( su && giu )
      return false;

    //negative
    if ( giu && !su )
    { //negative
      var_inv[i] = true;
      mytt = flip( mytt, i );
      //  std::cout << "x" << i+1 << "neg_un" << std::endl;
    }
  }

  //creating lp

  lprec* lp = NULL;
  int Ncol, *colno = NULL, j, sol = 0;
  REAL* row = NULL;
  Ncol = num_vars + 1; //+1 to include T
  const int T = Ncol;
  lp = make_lp( 0, Ncol );

  if ( lp == NULL )
  {
    return false; /* couldn't construct a new model... */
  }

  /* create space large enough for one row */
  colno = (int*)malloc( Ncol * sizeof( int ) );
  row = (REAL*)malloc( Ncol * sizeof( *row ) );

  if ( ( colno == NULL ) || ( row == NULL ) )
    return false;

  set_add_rowmode( lp, TRUE ); /* in order to create lp row by row */

  //I take on and off set
  std::vector<cube> on_set = isop( mytt );
  std::vector<cube> off_set = isop( unary_not( mytt ) );
  /* in substitution to isop the function get_prim_implicants_morreale
   * could be used */

//Constraints for on_set
  for ( cube i : on_set )
  {
    j = 0;
    for ( int k = 0; k < num_vars; k++ )
    {
      //I control if the variable is present in the cube
      if ( i.get_mask( k ) == 1 )
      {
        colno[j] = k + 1;
        /*put row[j]=1 since all variables in the sum must be summed */
        row[j] = 1;
        j++;
      }
    }
    colno[j] = T;
    /*-1 because T is brougth to the other member */
    row[j] = -1;
    j++;
    add_constraintex( lp, j, row, colno, GE, 0 );
  }

  //constraints for offset
  for ( cube i : off_set )
  {
    j = 0;
    for ( int k = 0; k < num_vars; k++ )
    {
      /*practically the same as before */
      if ( i.get_mask( k ) == 0 ) //variable not in the cube
      {
        colno[j] = k + 1;
        row[j] = 1;
        j++;
      }
    }
    colno[j] = T;
    row[j] = -1;
    j++;
    add_constraintex( lp, j, row, colno, LE, -1 );
  }

  /*it is not necessary to add the constraint
   * about the positivity of all variables
   * since it is ste by default by the lp
   * solver */

  set_add_rowmode( lp, FALSE );

  //sum of all variables plus T
  /* set the objective function */

  for ( int k = 0; k < Ncol; k++ )
  {
    colno[k] = k + 1;
     /* 1 in order to sum all variables */
    row[k] = 1;
  }
  set_obj_fnex( lp, Ncol, row, colno );

  /* set the object direction to minimize */
  set_minim( lp );
  /*the minimization is not mandatory:
   * in fact, by default, the solver
   * considers a minimization problem */

  set_verbose( lp, IMPORTANT );

 // print_lp( lp );

  sol = solve( lp );
  //if it is not a TF return out
  if ( sol != OPTIMAL )
    return false;

  //get variable values
  get_variables( lp, row );

  //forming the linear form
  for ( int i = 0; i < Ncol; i++ )
  {
    /* first I form linear form */
    linear_form.push_back( row[i] );
  }
  //then I change negated variables stored in var_inv
  for ( int i = 0; i < num_vars; i++ )
  {
    if ( var_inv[i] == true )
    {
      linear_form[i] = -linear_form[i];
      linear_form[Ncol - 1] = linear_form[Ncol - 1] + linear_form[i];
    }
  }

  if ( plf )
  {
    *plf = linear_form;
  }

  /* at the end of the algorithm I free memory used during lp */
  if ( row != NULL )
    free( row );
  if ( colno != NULL )
    free( colno );
  if(lp != NULL)
  {
    /* clean up such that all used memory by lpsolve is freed */
    delete_lp( lp );
  }

  return true;
}

} /* namespace kitty */

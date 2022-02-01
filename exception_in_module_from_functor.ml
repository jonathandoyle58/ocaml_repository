(*

#use "exception_in_module_from_functor.ml" ;;

This code produces triggers an incompletely displayed exception in the toplevel

*)

module Image = struct 

  let image f l=
  let rec tempf=(fun
   (graet,da_ober)->match da_ober with
   []->List.rev graet
   |a::peurrest->tempf(f(a)::graet,peurrest)
  ) in
  tempf([],l);;

end ;;  

module Option = struct 

  exception Unpackable of string;;

  module Private = struct 
  
  let unpack_with_error_message s=function
  None->raise(Unpackable(s))
  |Some(x)->x;;
  
  end ;;
  
  
  let add_element_on_the_right l x=match x with
    None->l
    |Some(a)->l@[a];;
   
  let rec filter_and_unpack f l=
   let rec filter0=(function
    (graet,da_ober)->match da_ober with
     []->List.rev(graet)
     |x::peurrest->match f(x) with
      None->filter0(graet,peurrest)
      |Some(y)->filter0(y::graet,peurrest)
   ) in
   filter0([],l);;
  
  let  find_and_stop f l=
   let rec find_and_stop0=(function
    da_ober->match da_ober with
     []->None
     |a::peurrest->match f(a) with
      None->find_and_stop0(peurrest)
      |Some(x)->Some(x)
   ) in
   find_and_stop0(l);;
  
  let propagate f=function
  None->None
  |Some(x)->Some(f(x));;
  
  let rec seek f =function
  []->None
  |a::b->if f(a) then Some(a) else seek(f)(b);;
  
  let unpack x =Private.unpack_with_error_message "void is not unpackable" x;;
  

end ;;  


module Ennig = struct 

  let doyle f a b=
  let accu=ref([]) in
  let rec doyle0=(function
  j->if j<a
     then (!accu)
   else let _=(accu:=f(j)::(!accu)) in doyle0(j-1)
  ) in
  doyle0 b;;
   
  
 let ennig a b=doyle (function x->x) a b;; 

 let index_everything l=
  let rec tempf=
   (function (j,graet,da_ober)->
     match da_ober with
      []->graet
     |a::b->tempf(j-1,(j,a)::graet,b)
    )    in
    tempf(List.length(l),[],List.rev(l));;
  
end ;;  

module Listennou = struct 

  
exception Ht_exn;;
exception Reposition_first_key_not_found;;
exception Reposition_second_key_not_found;;
exception Push_immediately_after_exn;;


let ht x=match x with
    []->raise(Ht_exn)
    |a::b->(a,b);;

let rec uncurrified_rev_append (x,y)=match x with
[]->y
|a::peurrest->uncurrified_rev_append (peurrest,a::y);;

let rec uncurrified_append (x,y)=uncurrified_rev_append (List.rev x,y);;

let factor (x,y)=
    let rec factor0=(fun
       (graet,da_ober1,da_ober2)->
       if (da_ober1=[])||(da_ober2=[])
       then (List.rev graet,da_ober1,da_ober2)
       else let (a1,peurrest1)=ht da_ober1
            and (a2,peurrest2)=ht da_ober2 in
            if a1=a2
            then factor0(a1::graet,peurrest1,peurrest2)
            else (List.rev graet,da_ober1,da_ober2)
    ) in
    factor0([],x,y);;

let comparable_for_prefix_order  a b=
    let (_,a1,b1)=factor(a,b) in (a1=[])||(b1=[]);;

let extends l1 l2=
   let (_,_,r2)=factor (l1,l2) in r2=[];;


let didrochan x=
let rec didrochan0=
(function (u,accu1,accu2,bowl)->match u with
 []->(accu1,accu2)
 |a::b->if bowl
        then didrochan0(b,a::accu1,accu2,false)
        else didrochan0(b,accu1,a::accu2,true))  
in
didrochan0(x,[],[],true);;

let find_index x ll=
let rec sub_f=
(function (j,l)->match l with
[]->(-1)      
|u::v->if u=x then j else sub_f(j+1,v)) in
sub_f(1,ll);;

exception Force_find_exn ;;

let rec force_find f x=
   match x with 
   [] -> raise(Force_find_exn)
   |a::others -> if f a 
                 then a 
                 else force_find f others ;; 

let morzholan f x=
let rec sub_f=(function (u,v)->if u=v then u else sub_f(v,f(v)))
in sub_f(x,f(x));;

let rec morzhol_bihan f k x=
if k=0 then x else morzhol_bihan f (k-1) (f(x));;

exception Big_rht_exn of int*int;;

let big_rht r l=let rec tempf=
(function (j,kleiz,dehou)->
if j=0 then (kleiz,dehou) else 
match dehou with
[]->raise(Big_rht_exn(r,List.length l))
|a::peurrest->tempf(j-1,a::kleiz,peurrest)
) in
tempf(r,[],l);;

let big_head r l=if (r>(List.length l)) then l else List.rev(fst(big_rht(r)(l)));;

let big_tail r l=if (r>(List.length l)) then [] else snd(big_rht(r)(l));;

let remove_element_at_idx l k=
   let (kleiz,dehou)=big_rht k l in 
   List.rev_append (List.tl kleiz) dehou;;

(* remove_element_at_idx [1; 2; 3; 4; 5; 6; 7] 3;; *)   

let decompose_wrt_two_indices l i j=
   let (r_part1,temp1)=big_rht (i-1) l in 
   let (ei,temp2)=ht temp1 in 
   let (r_part2,temp3)=big_rht (j-i-1) temp2 in 
   let (ej,part3)=ht temp3 in 
   (List.rev r_part1,ei,List.rev r_part2,ej,part3);;

(* decompose_wrt_two_indices [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] 3 7;; *)

let extract_interval l i j=
  let (r_part1,temp1)=big_rht (i-1) l in 
  let (r_part2,part3)=big_rht (j-i+1) temp1 in 
  (List.rev r_part1,List.rev r_part2,part3);;

(* extract_interval [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] 3 7;; *)

let decompose_wrt_element l elt1=
  let rec tempf=(
     fun (treated,to_be_treated)->match to_be_treated with 
     []->(List.rev treated,false,[])
    |elt::other_elts ->
       if elt=elt1
      then (List.rev(treated),true,other_elts)
      else tempf(elt::treated,other_elts)
  ) in 
  tempf([],l);; 

(* decompose_wrt_element [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] 3;; *)



let reposition_by_putting_snd_immediately_after_fst l elt_i elt_j=
    let (left1,found1,right1)=decompose_wrt_element l elt_i in 
    if not found1 then raise(Reposition_first_key_not_found) else 
    let (left2,found2,right2)=decompose_wrt_element right1 elt_j in 
    if not found2 then raise(Reposition_second_key_not_found) else
    left1@(elt_i::elt_j::(left2@right2));; 
  
(* reposition_by_putting_snd_immediately_after_fst [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] 3 7;; *)  


let power_set l=
let rec tempf=
(function (da_ober,graet)->match da_ober with
[]->graet
|a::peurrest->tempf(peurrest,graet@(Image.image(function y->a::y)(graet)))
) in
tempf(List.rev(l),[[]]);;


let fold_right f x0 l=List.fold_left(function x->(function a->f a x)) x0 l;;



let universal_delta_list l=
let rec sub_f=
(function (accu,a,rl)->match rl with
[]->List.rev(accu)
|b::x->sub_f((a,b)::accu,b,x)
) in
match l with
[]->[]
|u::v->sub_f([],u,v);;

 
let delete_redundancies r l=
 let rec tempf=(function
   (graet,da_ober)->match da_ober with
   []->List.rev(graet)
   |x::peurrest->
     if List.exists(function y->r y x)(peurrest)
     then tempf(graet,peurrest)
     else let temp1=List.filter(function y->not(r x y))(peurrest) in
          tempf(x::graet,temp1)
 ) in
 tempf([],l);;

let nonredundant_version l=
  let rec tempf=(
    fun (graet,da_ober)->
      match da_ober with
      []->List.rev graet
      |a::peurrest->if List.mem a graet
                    then tempf(graet,peurrest)
                    else tempf(a::graet,peurrest)
  ) in
  tempf([],l);;

let rev_map f l=
   let rec tempf=(
     fun (graet,da_ober)->match da_ober with
     []->graet
     |a::peurrest->tempf((f a)::graet,peurrest)
   ) in
   tempf([],l);;
   
let redundant_indices l=
  let rec tempf=(
    fun (counter,already_known,bad_indices,to_be_treated)->
      match to_be_treated with
      []->List.rev bad_indices
      |a::others->
        let idx=counter+1 in  
        if List.mem a already_known
        then tempf(idx,already_known,idx::bad_indices,others)
        else tempf(idx,a::already_known,bad_indices,others)
  ) in
  tempf(0,[],[],l);;

(*
redundant_indices [1; 2; 1; 4; 5; 6; 3; 8; 9; 10; 11; 12; 13; 6; 15];;
*)

let divide_by_two l=
   let rec tempf=(
     fun (treated,to_be_treated)->match to_be_treated with 
     []->(List.rev treated,None)
     |a1::others1->(
         match others1 with 
         []->(List.rev treated,Some(a1))
         |a2::others->tempf((a1,a2)::treated,others)
      )
   ) in 
   tempf ([],l);;

let push_immediately_after l elt2 elt1 =
  let rec tempf=(
    fun (treated,to_be_treated)->match to_be_treated with 
     []->raise(Push_immediately_after_exn)
    |elt::others ->
      if elt=elt1
      then List.rev_append treated (elt::elt2::others)
      else tempf(elt::treated,others)
  ) in 
  tempf([],l);; 

let hi=List.length;;
let rev=List.rev;;

(*

push_immediately_after [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12] 145 3;;

*)

let partition_from_set_of_ranges l n=
    if l=[] then [1,n,false] else 
    let (last_i,last_j)=List.hd(List.rev l) 
    and (first_i,_)=List.hd l in
    let temp2=universal_delta_list l in  
    let temp3=Image.image (fun ((i1,j1),(i2,j2))->
      [(i1,j1,true);(j1+1,i2-1,false)]
    ) temp2 in 
    let middle_part=List.flatten temp3 in
    let first_part=(if first_i>1 then [(1,first_i-1,false)] else []) 
    and last_part=(if last_j<n then [(last_j+1,n,false)] else []) in 
    first_part@middle_part@[(last_i,last_j,true)]@last_part;;

(*

partition_from_set_of_ranges [(3,7);(41,52)] 100;;
partition_from_set_of_ranges [(1,7);(41,52)] 100;;

*)

let extract_intervals_in_complement l n =
   let enhanced_l = 0::(l@[n+1]) in 
   let temp1=universal_delta_list enhanced_l in
   let temp2= Image.image (fun (x,y)->(x+1,y-1)) temp1 in 
   List.filter (fun (a,b)->a<=b) temp2;;

(*

extract_intervals_in_complement [3;7;8;20] 30;;
extract_intervals_in_complement [1;7;8;20] 30;;
extract_intervals_in_complement [1;7;8;30] 30;;

*)   

let complement_union_of_ranges ranges n=
   let rec tempf=(fun 
     (already_treated,a,b,to_be_treated)->
       match to_be_treated with 
       []->List.rev((a,b)::already_treated)
       |(x1,y1)::other_ranges->
         tempf((a,x1-1)::already_treated,y1+1,b,other_ranges)
   ) in 
   let temp1=tempf([],1,n,ranges) in 
   List.filter (fun (x,y)->x<=y) temp1;;

(*

complement_union_of_ranges [3,7;8,20] 30;;
complement_union_of_ranges [3,7;9,20] 30;;
complement_union_of_ranges [1,7;9,20] 30;;
complement_union_of_ranges [1,7;9,30] 30;;
complement_union_of_ranges [1,7;8,30] 30;;

*)


let split_list_in_half l=
   let temp1=Ennig.index_everything(l) in 
   let (temp2,temp3)=List.partition (fun (j,_)->(j mod 2)=1) temp1 in 
   (Image.image snd temp2,Image.image snd temp3);;

(*

split_list_in_half [1; 2; 3; 4; 5; 6; 7];;
split_list_in_half [1; 2; 3; 4; 5; 6; 7; 8];;

*)   



let unequal_combine l1 l2 =
   let rec tempf=(fun
     (treated,to_be_treated1,to_be_treated2)->
       match to_be_treated1 with 
       []->List.rev(treated)
       |a1::others1->(
                       match to_be_treated2 with 
                        []->List.rev(treated)
                        |a2::others2 -> tempf((a1,a2)::treated,others1,others2)
                     )
   ) in 
   tempf([],l1,l2);;

exception Fst_is_largest of int * int;;
  

let unequal_combine_where_fst_is_smallest l1 l2 =
   let n1=List.length(l1) and n2=List.length(l2) in 
   if n1>n2 then raise(Fst_is_largest(n1,n2)) else   
   unequal_combine l1 l2;;


exception  Extract_successive_pairs_exn of int;;

let extract_successive_pairs_from_even_list l=
   let m1 =(List.length l) in 
   if (m1 mod 2)<>0 then raise(Extract_successive_pairs_exn(m1)) else 
   let m2=m1/2 in 
   Ennig.doyle (fun j->
      (List.nth l (2*j-2),List.nth l (2*j-1)) 
   ) 1 m2;;

let remove_initial_contaminated_elements contamination_test all_elts =
      let rec tempf =(
         fun (beginning,l)-> match l with 
         [] -> (beginning,[])
         |a :: b -> if  contamination_test a 
                    then tempf (a::beginning,b) 
                    else (beginning,l)
      ) in 
      tempf ([],all_elts) ;;

(*

remove_initial_contaminated_elements (fun x->x<=100) [2;3;507;1;4;30];;

*)

let start_separating is_sep is_not_sep elts =
     let (_,temp1) = remove_initial_contaminated_elements is_sep elts in 
     remove_initial_contaminated_elements is_not_sep temp1;; 
      
let separate_according_to elts separators =      
   let is_sep  = (fun x->List.mem x separators) 
   and is_not_sep = (fun x->not(List.mem x separators))  in 
   let rec tempf = (fun (treated,to_be_treated)-> 
       if to_be_treated=[]
       then List.rev treated 
      else let (half1,half2)= start_separating is_sep is_not_sep to_be_treated in 
           let treated2 =(
                if half1=[] 
                then treated 
                else (List.rev half1)::treated 
           ) in 
           tempf(treated2,half2)          
   ) in 
   tempf([],elts);;

(*

separate_according_to  [1;2;3;0;4;0;0;5;6;0;0;0;7;0;8;0] [0];;
separate_according_to  [0;0;1;2;3;0;4;0;0;5;6;0;0;0;7;0;8;0] [0];;
*)


let partition_according_to_fst pairs=
  let rec tempf = (fun (already_treated,to_be_treated)->
       match to_be_treated with 
        [] -> List.rev already_treated 
       |(a0,_) :: _ ->
         let (part1,part2) = List.partition (fun (a,b)->a=a0) to_be_treated in 
         tempf ((a0,Image.image snd part1)::already_treated,part2)     
   ) in 
   tempf ([],pairs) ;;
  
exception Compute_largest_connected_interval_on_the_left_exn ;;

let compute_largest_connected_interval_on_the_left initial_l =
  let rec tempf = (fun  (a,b,l)->
   match l with 
   [] -> ((a,b),[])
   |head :: tail -> if head = b+1 
                    then tempf(a,b+1,tail)
                    else ((a,b),l)  
  ) in  
  match initial_l with 
  [] -> raise Compute_largest_connected_interval_on_the_left_exn
  | head2 :: tail2 -> tempf (head2,head2,tail2) ;;

let decompose_into_connected_components l=
  let rec tempf = (fun 
     (treated,to_be_treated)->
     if to_be_treated = [] then List.rev treated else 
     let (interval,others) =  compute_largest_connected_interval_on_the_left to_be_treated in 
     tempf (interval::treated,others)
  ) in 
  tempf ([],l);;

(*

decompose_into_connected_components [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40;
 41; 42; 43; 44; 45; 46; 47; 48];;

*)


let replace_if_possible l x=
  match List.assoc_opt x l with 
  None -> x 
  |Some y -> y ;;

end ;;  

module Total_ordering_result_t = struct 

  type t =
   Lower 
 | Equal 
 | Greater ;;

end ;;  

module Total_ordering_t = struct 

  type 'a t = ( 'a -> 'a ->Total_ordering_result_t.t ) ;;

end ;;  

module Total_ordering = struct 


  module Private = struct
    let leq (computer:'a Total_ordering_t.t) x y=
       let v=computer(x)(y) in
       (v=Total_ordering_result_t.Lower)||(v=Total_ordering_result_t.Equal);;
       
     let lt (computer:'a Total_ordering_t.t) x y=(computer(x)(y)=Total_ordering_result_t.Lower);;   
     
     let geq (computer:'a Total_ordering_t.t) x y=
       let v=computer(x)(y) in
       (v=Total_ordering_result_t.Lower)||(v=Total_ordering_result_t.Equal);;
       
     let gt (computer:'a Total_ordering_t.t) x y=(computer(x)(y)=Total_ordering_result_t.Greater);;   
     
     let from_lt f=
       let temp1=(fun x y->
         if f(x)(y)
         then Total_ordering_result_t.Lower
         else if f(y)(x)
              then Total_ordering_result_t.Greater
              else Total_ordering_result_t.Equal
       ) in
       (temp1:'a Total_ordering_t.t);;
     
     let standard_completion f g=
      let answer=(fun x y->
       if f(y)(x)
       then Total_ordering_result_t.Greater
       else if f(x)(y)
            then Total_ordering_result_t.Lower
            else if g(x)(y)
                 then Total_ordering_result_t.Equal
                 else if x<y
                      then Total_ordering_result_t.Lower
                      else Total_ordering_result_t.Greater
      ) in
      (answer: 'a Total_ordering_t.t);;
     
     let standard=((fun x y->
        if x=y
        then Total_ordering_result_t.Equal
        else if x<y
             then Total_ordering_result_t.Lower
             else Total_ordering_result_t.Greater
     ): 'a Total_ordering_t.t);;
     
    let standard2=((fun (x1,y1) (x2,y2)->
        let t1=standard x1 x2 in 
        if t1<> Total_ordering_result_t.Equal 
        then t1
        else standard y1 y2
     ): ('a * 'b) Total_ordering_t.t);;
    
     let completion f (g:'a Total_ordering_t.t)=
      let answer=(fun x y->
       if f(y)(x)
       then Total_ordering_result_t.Greater
       else if f(x)(y)
            then Total_ordering_result_t.Lower
             else g(x)(y)
      ) in
      (answer: 'a Total_ordering_t.t);;
     
    let combine=((fun ~tried_first ~tried_second->
      (fun x y->
       let first_trial = tried_first x y in 
       if first_trial <> Total_ordering_result_t.Equal 
       then first_trial
       else tried_second x y
      ) ): 
        tried_first:('a Total_ordering_t.t) -> tried_second:('a Total_ordering_t.t) -> ('a Total_ordering_t.t)
      );;
    
     let product (f:'a Total_ordering_t.t) (g:'b Total_ordering_t.t)=
      ((fun (x1,y1) (x2,y2)->
         let t=f(x1)(x2) in
         if t<>Total_ordering_result_t.Equal 
         then t
         else g y1 y2
     ): ('a*'b) Total_ordering_t.t);;
     
     let triple_product (f:'a Total_ordering_t.t) (g:'b Total_ordering_t.t) (h:'c Total_ordering_t.t)=
      ((fun (x1,y1,z1) (x2,y2,z2)->
         let tx=f(x1)(x2) in
         if tx<>Total_ordering_result_t.Equal 
         then tx
         else let ty=g(y1)(y2) in
              if ty<>Total_ordering_result_t.Equal 
              then ty
              else h z1 z2
     ): ('a*'b*'c) Total_ordering_t.t);;
     
     let rec lex_compare (f:'a Total_ordering_t.t)=
      let rec tempf=(
        fun l1 l2->
         match l1 with 
         []->(if l2=[] then Total_ordering_result_t.Equal else Total_ordering_result_t.Lower)
         |a1::b1->
          (
            match l2 with 
            []->Total_ordering_result_t.Greater
            |a2::b2->
              let t=f(a1)(a2) in
               if t<>Total_ordering_result_t.Equal then t else
               tempf b1 b2
          )) in
         (tempf:>( ('a list) Total_ordering_t.t));;
     
    
    
    let silex_compare (f:'a Total_ordering_t.t)=
      let tempf=(
        fun l1 l2->
         let t=standard(List.length l1)(List.length l2) in
         if t<>Total_ordering_result_t.Equal then t else
         lex_compare f l1 l2
      ) in
       (tempf:>( ('a list) Total_ordering_t.t));;
     
    
    let from_list (l:'a list)=
      let tempc=(fun x y->
      let rec tempf=(function
       []->(x<y)
       |u::peurrest->if u=x then List.mem(y)(peurrest)
                     else if u=y then false
                     else tempf(peurrest)
      ) in
      tempf l) in
      from_lt tempc;;
    
    let min (f:'a Total_ordering_t.t)=function
     []->failwith("Min of the empty set is undefined")
     |a::b->
       let rec tempf=(fun
        (candidate,l)->match l with
          []->candidate
          |c::peurrest->if f(c)(candidate)=Total_ordering_result_t.Lower
                        then tempf(c,peurrest)
                        else tempf(candidate,peurrest)
       ) in
       tempf(a,b);;
    
    let max (f:'a Total_ordering_t.t)=function
     []->failwith("Max of the empty set is undefined")
     |a::b->
       let rec tempf=(fun
        (candidate,l)->match l with
          []->candidate
          |c::peurrest->if f(c)(candidate)=Total_ordering_result_t.Greater
                        then tempf(c,peurrest)
                        else tempf(candidate,peurrest)
       ) in
       tempf(a,b);;
       
    let minimize_it_with_care (cf:'a Total_ordering_t.t) 
       f=function
    []->failwith("careful min on empty set undefined")
    |x::y->
     let rec minimize_it_with_care0=(function
      (current_candidates,current_value,da_ober)->match da_ober with
      []->(current_value,List.rev(current_candidates))
      |a::peurrest->let va=f(a) in
                    let howl=cf(va)(current_value) in
                    if howl=Total_ordering_result_t.Lower
            then minimize_it_with_care0([a],va,peurrest)
            else if howl=Total_ordering_result_t.Equal
                 then minimize_it_with_care0(a::current_candidates,current_value,peurrest)
               else minimize_it_with_care0(current_candidates,current_value,peurrest)
     ) 
    in
     minimize_it_with_care0([x],f(x),y);;
    
    
    let maximize_it_with_care (cf:'a Total_ordering_t.t) 
       f=function
    []->failwith("careful max on empty set undefined")
    |x::y->
     let rec maximize_it_with_care0=(function
      (current_candidates,current_value,da_ober)->match da_ober with
      []->(current_value,List.rev(current_candidates))
      |a::peurrest->let va=f(a) in
                    let howl=cf(va)(current_value) in
                    if howl=Total_ordering_result_t.Greater
            then maximize_it_with_care0([a],va,peurrest)
            else if howl=Total_ordering_result_t.Equal
                 then maximize_it_with_care0(a::current_candidates,current_value,peurrest)
               else maximize_it_with_care0(current_candidates,current_value,peurrest)
     ) 
    in
     maximize_it_with_care0([x],f(x),y);;
    
    let modify_locally (f:'a Total_ordering_t.t) l=
      let big_m=max(f)(l) in
      let tempf=(fun x y->
        if List.mem(x)(l)
        then if List.mem(y)(l)
             then if x=y
                  then Total_ordering_result_t.Equal
                  else (from_list l x y)
             else f big_m y
        else if List.mem(y)(l)
             then f x big_m
             else f x y
      
      ) in
      (tempf:>( 'a Total_ordering_t.t));;
    
    let list_for_dictionary_order=
      [97; 65; 98; 66; 99; 67; 100; 68; 101; 69; 102; 70; 103; 71; 104; 72; 105;
      73; 106; 74; 107; 75; 108; 76; 109; 77; 110; 78; 111; 79; 112; 80; 113; 81;
      114; 82; 115; 83; 116; 84; 117; 85; 118; 86; 119; 87; 120; 88; 121; 89;
      122; 90; 91; 92; 93; 94; 95; 96];;  
    
    let reindexer_for_dictionary_order i=
        if (i<65)||(i>122) 
        then i 
        else 64+(Listennou.find_index i list_for_dictionary_order);;
    
    
    let for_characters=let tempf=(fun x y->
      standard 
            (reindexer_for_dictionary_order(int_of_char x))
            (reindexer_for_dictionary_order(int_of_char y))
      ) in (tempf:>char Total_ordering_t.t);;
    
    let for_integers=let tempf=(fun (x:int) (y:int)-> standard x y 
        ) in (tempf:>int Total_ordering_t.t);;  
    
    let lex_for_strings=
        ((fun s1 s2->
          let m1=String.length s1
          and m2=String.length s2
          in
          let m=Stdlib.min(m1)(m2) in
          match Option.seek (fun j->(String.get s1 j)<>(String.get s2 j)) (Ennig.ennig 0 (m-1)) with
          None->standard m1 m2
          |Some(j)->for_characters (String.get s1 j) (String.get s2 j) 
        ) : string Total_ordering_t.t);;
    
    let silex_for_strings=
          ((fun s1 s2->
            let m1=String.length s1
            and m2=String.length s2
            in
            let first_try=standard(m1)(m2) in
            if first_try<>Total_ordering_result_t.Equal
            then first_try
            else lex_for_strings s1 s2
          ) : string Total_ordering_t.t);;    
    
    let lex_for_string_lists=
      ((fun l1 l2->
          let (_,left_part,right_part)=Listennou.factor (l1,l2) in
          if left_part=[] 
          then (if right_part=[] 
               then Total_ordering_result_t.Equal 
               else Total_ordering_result_t.Lower)
          else if right_part=[] 
               then Total_ordering_result_t.Greater 
               else lex_for_strings (List.hd left_part) (List.hd right_part)  
      ) : (string list) Total_ordering_t.t);;
    
    let for_longest_match=  
        ((fun s1 s2->
          let m1=String.length s1
          and m2=String.length s2 in
          if (
              if m1>m2 then false else
              (String.sub s2 0 m1)=s1
          ) then Total_ordering_result_t.Greater else
          if (
              if m2>m1 then false else
              (String.sub s1 0 m2)=s2
          ) then Total_ordering_result_t.Lower else
          lex_for_strings s1 s2
         ): string Total_ordering_t.t);;
    
    
    let for_longest_match_pairs=  
    ((fun (s1,v1) (s2,v2)->
      let first_try=silex_for_strings(s2)(s1) in
      if first_try<>Total_ordering_result_t.Equal 
      then first_try
      else standard v1 v2
     ): (string*'b) Total_ordering_t.t);;
     
    let from_snd (f:'b Total_ordering_t.t)=((fun (x1,y1) (x2,y2)->
      let first_try=f y1 y2 in
      if first_try<>Total_ordering_result_t.Equal 
      then first_try
      else standard x1 x2
    ): ('a*'b) Total_ordering_t.t );;
    
    let cardinality_then_diameter =((fun l1 l2->
      let first_try=standard (List.length l1) (List.length l2) in
      if first_try<>Total_ordering_result_t.Equal 
      then first_try
      else 
      let diam1 = List.hd(List.rev l1) - (List.hd l1)
      and diam2 = List.hd(List.rev l2) - (List.hd l2) in 
      let second_try=standard diam1 diam2 in
      if second_try<>Total_ordering_result_t.Equal 
      then second_try
      else lex_compare for_integers l1 l2
    ): (int list) Total_ordering_t.t );;
    
    end ;;
    
    let cardinality_then_diameter = Private.cardinality_then_diameter ;;
    let for_integers = Private.for_integers ;;
    let lex_compare = Private.lex_compare ;;
    let lex_for_strings = Private.lex_for_strings ;;
    let product = Private.product ;;
    let silex_compare = Private.silex_compare ;;
    let silex_for_strings = Private.silex_for_strings ;;
    let silex_for_intlists = Private.silex_compare for_integers ;;
    let standard = Private.standard ;;
    let standard2 = Private.standard2 ;;
    
end ;;  

module Ordered = struct 

  module Private = struct 

    let intersect (cmpr:'a Total_ordering_t.t) ox oy=
        let rec tempf=(function (u,v,accu)->
          if u=[] then (List.rev(accu)) else
          if v=[] then (List.rev(accu)) else
          let xu=List.hd(u) and yu=List.tl(u) 
          and xv=List.hd(v) and yv=List.tl(v) in
          match cmpr(xu)(xv) with
           Total_ordering_result_t.Lower->tempf(yu,v,accu)
          |Total_ordering_result_t.Equal->tempf(yu,yv,xu::accu)
          |Total_ordering_result_t.Greater->tempf(u,yv,accu)
        ) in
        tempf(ox,oy,[]);;
    
    let is_increasing (cmpr:'a Total_ordering_t.t) l=
      if List.length(l)<2 then true else
      let rec tempf=(function
      (a,to_be_treated)->match to_be_treated with
       []->true
       |b::others->if (cmpr(a)(b)=Total_ordering_result_t.Lower)
                     then tempf(b,others)
                     else false
      ) in
      tempf(List.hd l,List.tl l);;
      
    
    let merge (cmpr:'a Total_ordering_t.t) ox oy=
        let rec tempf=(function (u,v,accu)->
          if u=[] then (List.rev_append(accu)(v)) else
          if v=[] then (List.rev_append(accu)(u)) else
          let xu=List.hd(u) and yu=List.tl(u) 
          and xv=List.hd(v) and yv=List.tl(v) in
        match cmpr(xu)(xv) with
          Total_ordering_result_t.Lower->tempf(yu,v,xu::accu)
        |Total_ordering_result_t.Equal->tempf(yu,yv,xu::accu)
        |Total_ordering_result_t.Greater->tempf(u,yv,xv::accu)
        ) in
        tempf(ox,oy,[]);;
    
    
    let setminus (cmpr:'a Total_ordering_t.t) ox oy=
        let rec tempf=
        (function (u,v,accu)->
          if u=[] then (List.rev(accu)) else
          if v=[] then (List.rev_append(accu)(u)) else
          let xu=List.hd(u) and yu=List.tl(u) 
          and xv=List.hd(v) and yv=List.tl(v) in
          match cmpr(xu)(xv) with
             Total_ordering_result_t.Lower->tempf(yu,v,xu::accu)
            |Total_ordering_result_t.Equal->tempf(yu,yv,accu)
            |Total_ordering_result_t.Greater->tempf(u,yv,accu)
       ) in
       tempf(ox,oy,[]);;
    
    let rec sort (cmpr:'a Total_ordering_t.t) x=
      if List.length(x)<2
      then x
      else let temp1=Listennou.split_list_in_half(x) in
           let y1=sort(cmpr)(fst temp1)
           and y2=sort(cmpr)(snd temp1) in
           merge cmpr y1 y2;;
    
    let is_included_in (cmpr:'a Total_ordering_t.t) ox oy=
           let rec tempf=(function (u,v)->
             if u=[] then true else
             if v=[] then false else
             let xu=List.hd(u) and yu=List.tl(u) 
             and xv=List.hd(v) and yv=List.tl(v) in
             match cmpr(xu)(xv) with
               Total_ordering_result_t.Lower->false
             |Total_ordering_result_t.Equal->tempf(yu,yv)
             |Total_ordering_result_t.Greater->tempf(u,yv)
           ) in
           tempf(ox,oy);;       
    
    let helper1_for_minimal_elements_selection (cmpr:'a Total_ordering_t.t)  
           comparator =
           let rec tempf = (fun
           (treated,to_be_treated) -> match to_be_treated with 
           [] -> (None,List.rev treated) 
          |new_item :: others ->
             if new_item = comparator 
             then (* ignore and continue *) tempf (treated,others)
             else       
             if is_included_in cmpr new_item comparator
             then (* finish *)  (Some new_item,[])
             else 
             if is_included_in cmpr comparator new_item
             then tempf (treated,others)
             else tempf (new_item::treated,others)  
           ) in tempf ;;    
         
    let rec helper2_for_minimal_elements_selection (cmpr:'a Total_ordering_t.t)  =
            let rec tempf = (fun 
           (treated,to_be_treated) -> match to_be_treated with 
            [] -> List.rev treated 
           |new_item :: others ->
             let (opt,checked_subset) = 
               helper1_for_minimal_elements_selection cmpr new_item ([],others) in 
             if opt<>None 
             then tempf(treated,others) 
             else tempf(new_item::treated,checked_subset)) in   
           tempf ;;
             
    let select_minimal_elements_for_inclusion tr ll=
           helper2_for_minimal_elements_selection tr ([],ll) ;;
      
    
    end;;
    
    
    let diff (cmpr: 'a Total_ordering_t.t) =
              let rec tempf=(fun
                (treated_bc,treated_b,treated_c,to_be_treated1,to_be_treated2)->
                  match to_be_treated1 with
                  []->(treated_bc,treated_b,List.rev_append treated_c to_be_treated2)
                  |(a1,b1)::others1->
                  (
                    match to_be_treated2 with
                  []->(treated_bc,List.rev_append treated_b to_be_treated1,treated_c)     
                  |(a2,c2)::others2->
                    (
                      match cmpr a1 a2 with
                      Total_ordering_result_t.Lower->
                        tempf(treated_bc,(a1,b1)::treated_b,treated_c,others1,to_be_treated2)
                      |Total_ordering_result_t.Greater->
                      tempf(treated_bc,treated_b,(a2,c2)::treated_c,to_be_treated1,others2)
                      |Total_ordering_result_t.Equal->
                      tempf((a1,b1,c2)::treated_bc,treated_b,treated_c,others1,others2)  
                    )
                  )      
              ) in
              tempf;;   
    
    let does_not_intersect (cmpr:'a Total_ordering_t.t) ox oy=
        let rec tempf=(function (u,v)->
            if (u=[])||(v=[]) then true else
            let xu=List.hd(u) and yu=List.tl(u) 
            and xv=List.hd(v) and yv=List.tl(v) in
            match cmpr(xu)(xv) with
              Total_ordering_result_t.Lower->tempf(yu,v)
            |Total_ordering_result_t.Equal->false
            |Total_ordering_result_t.Greater->tempf(u,yv)
        ) in
        tempf(ox,oy);;
    
    exception Empty_intersection_undefined;;    
    
    let fold_intersect cmpr=function
       []->raise(Empty_intersection_undefined)
      |a::b->List.fold_left(Private.intersect cmpr)(a)(b);;
    
    let fold_merge cmpr l=
       let rec tempf=(function
          (already_treated,to_be_treated)->match to_be_treated with 
          []->already_treated
          |a::b->tempf(Private.merge cmpr a already_treated,b)
       ) in 
       tempf([],l);;    
    
    let insert cmpr x oy=Private.merge cmpr [x] oy;; 
    
    let intersect = Private.intersect;;
    
    let intersects cmpr ox oy = not(does_not_intersect cmpr ox oy);;
    
    let is_included_in = Private.is_included_in ;;
    
    let rec mem (cmpr:'a Total_ordering_t.t) x ol=
       let rec tempf=(function
        []->false
        |a::others->match cmpr(x)(a) with
           Total_ordering_result_t.Lower->false
           |Total_ordering_result_t.Equal->true
           |Total_ordering_result_t.Greater->tempf others
       )  in
       tempf ol;;    
    
    let merge = Private.merge;;
    
    let outsert cmpr x oy=Private.setminus cmpr oy [x];;
    
    let safe_set cmpr ox=if Private.is_increasing(cmpr)(ox) 
                         then ox 
                         else Private.sort cmpr ox;;
    
    let select_minimal_elements_for_inclusion = Private.select_minimal_elements_for_inclusion;;
    
    let setminus = Private.setminus;;
    
    let sort = Private.sort;;
  
    let symmetric_difference cmpr x y =
      merge cmpr (setminus cmpr x y) (setminus cmpr y x) ;;
    
    
end ;;  


module Uple = struct 

  let list_of_pairs l=
  if List.length(l)<2 then [] else
  let rec sub_f=(function
  (accu,ll)->match ll with
  []->List.rev(accu)
  |a::b->sub_f(List.rev_append(List.rev(List.rev_map(function t->(a,t))(b)))(accu),b)
  ) in
  sub_f([],l);;  

end ;;  

module Memoized = struct

  type ('a,'b) map=('a->'b);;
   
  let recursive_from=((fun (big_f:('a->'b)->'a->'b) (a_hashtbl_for_f:('a,'b) Hashtbl.t)->
    let rec memoized_f=(fun x->
       if Hashtbl.mem(a_hashtbl_for_f)(x)
       then Hashtbl.find(a_hashtbl_for_f)(x)
       else let mf=(memoized_f:>('a->'b)) in
            let y=big_f(mf)(x) in
            let ()=(Hashtbl.add(a_hashtbl_for_f) x y) in
            y
    ) in
    memoized_f):>(('a->'b)-> 'a -> 'b) -> (('a,'b) Hashtbl.t) -> ('a, 'b) map);;
  
  let recursive (big_f:('a->'b)->'a->'b)=
    let a_hashtbl_for_f=Hashtbl.create(100) in
    recursive_from big_f a_hashtbl_for_f;;

end ;;  

module Ordered_misc = struct 

  let oi = Total_ordering.for_integers ;;

  let rec helper_for_minimal_elts_wrt_inclusion (already_treated,to_be_treated) =
    match to_be_treated with 
    [] -> List.rev already_treated 
    | a :: others ->
       if List.exists (fun b->
         (b<>a) && ( Ordered.is_included_in oi b a) ) others
       then helper_for_minimal_elts_wrt_inclusion (already_treated,others)
       else 
        let temp1 = List.filter (fun b->
           not(Ordered.is_included_in oi a b)) others in
        helper_for_minimal_elts_wrt_inclusion (a :: already_treated,temp1) ;;  

    let minimal_elts_wrt_inclusion l= 
        helper_for_minimal_elts_wrt_inclusion ([],l) ;;

end ;;  


module Sz_max_width_t = struct 

  type t = MW of int ;;

end ;;  

module Sz_preliminaries = struct 


  module Private = struct

    let i_setminus = Ordered.setminus Total_ordering.for_integers  ;;  
    let i_sort = Ordered.safe_set Total_ordering.for_integers  ;;
    let i_is_included_in = Ordered.is_included_in Total_ordering.for_integers ;;
    let il_merge = Ordered.merge Total_ordering.silex_for_intlists ;;
    let il_sort = Ordered.safe_set Total_ordering.silex_for_intlists ;;
    
    let diameter soi =
      if List.length(soi)<2 then 0 else 
      (List.hd(List.rev soi)) - (List.hd soi) + 1  ;; 
    
    let look_for_arithmetic_progressions_in_with_width_equal_to
             soi width=
      if List.length(soi)<3 then [] else 
      let temp1 = Image.image (fun x->[x;x+width;x+2*width]) soi in 
      List.filter (fun obstruction -> i_is_included_in obstruction soi) temp1 ;;  
    
    let look_for_arithmetic_progressions_in_with_width_up_to 
      (Sz_max_width_t.MW width) soi=
      let max_width = (if width<1 then ((diameter soi)-1)/2 else width) in 
      List.rev(List.flatten(Ennig.doyle 
      (look_for_arithmetic_progressions_in_with_width_equal_to soi) 1 max_width));;
      
  
    let test_for_admissibility max_width soi = 
        ((look_for_arithmetic_progressions_in_with_width_up_to max_width soi) = [])
    
    let extender max_width ll x=
      let temp1 = Image.image (fun y->i_sort (y@[x])) ll in 
      let temp2 = List.filter (test_for_admissibility max_width) temp1 in
      il_merge ll temp2 ;;
    
    let restricted_power_set =Memoized.recursive (fun old_f (max_width,soi) ->
      if soi = [] 
      then [[]]  
      else 
      let temp1 = List.rev soi in 
      let (last_elt,temp2) = Listennou.ht temp1 in 
      let soi2 = List.rev temp2 in 
      extender max_width (old_f (max_width,soi2)) last_elt  
    );;
    
    let arithmetic_progressions_in_interval_with_width_equal_to (a,b) width  =
      Ennig.doyle (fun x->[x;x+width;x+2*width]) a (b-2*width)  ;; 
    
    let arithmetic_progressions_with_width_up_to_in_interval 
      interval (Sz_max_width_t.MW width)  = 
      let (a,b) = interval in 
      let max_width = (if width<1 then (b-a)/2 else width) in 
      List.rev(List.flatten(Ennig.doyle 
      (arithmetic_progressions_in_interval_with_width_equal_to interval) 1 max_width));;  ;;   
    
    let force_subset_in_arbitrary_set (Sz_max_width_t.MW width) subset soi =
        let old_obses = look_for_arithmetic_progressions_in_with_width_up_to 
        (Sz_max_width_t.MW width) soi in 
        let new_obses = Option.filter_and_unpack (
          fun old_obstruction ->
            let new_obstruction = i_setminus old_obstruction subset in
            if (new_obstruction = old_obstruction) || (new_obstruction = []) 
            then None 
            else Some new_obstruction  
        ) old_obses in 
        Ordered_misc.minimal_elts_wrt_inclusion (il_sort new_obses);;
    
    
    let force_subset_in_interval (Sz_max_width_t.MW width) subset interval =
        let old_obses = arithmetic_progressions_with_width_up_to_in_interval interval (Sz_max_width_t.MW width) in 
        let new_obses = Option.filter_and_unpack (
          fun old_obstruction ->
            let new_obstruction = i_setminus old_obstruction subset in
            if (new_obstruction = old_obstruction) || (new_obstruction = []) 
            then None 
            else Some new_obstruction  
        ) old_obses in 
        Ordered_misc.minimal_elts_wrt_inclusion (il_sort new_obses);;
    
    end ;;
    
  
    let contained_arithmetic_progressions = Private.look_for_arithmetic_progressions_in_with_width_up_to ;;
    let force_subset_in_arbitrary_set = Private.force_subset_in_arbitrary_set ;;
    let force_subset_in_interval = Private.force_subset_in_interval ;;
    let restricted_power_set = Private.restricted_power_set ;;
    let test_for_admissibility = Private.test_for_admissibility ;;  

end ;;  

module Basic = struct 

  let fold_sum=function
  []->0
  |a::b->List.fold_left(+)(a)(b);;

end ;;  

module Max = struct 

  let list=function 
  []->failwith("max of empty set undefined according to Garfield")
  |a::b->List.fold_left(max)(a)(b);;

  let maximize_it_with_care f=function
  []->failwith("careful max on empty set undefined")
  |x::y->
   let rec maximize_it_with_care0=(function
    (current_candidates,current_value,da_ober)->match da_ober with
    []->(current_value,List.rev(current_candidates))
    |a::peurrest->let va=f(a) in
                  if (va>current_value)
          then maximize_it_with_care0([a],va,peurrest)
          else if (va=current_value)
               then maximize_it_with_care0(a::current_candidates,current_value,peurrest)
             else maximize_it_with_care0(current_candidates,current_value,peurrest)
   ) 
  in
   maximize_it_with_care0([x],f(x),y);;

end ;;  


let basic_string_of_il l = "["^(String.concat ";" (Image.image string_of_int l))^"]" ;;
let string_of_interval (a,b) =
    if b-a<=2 then basic_string_of_il(Ennig.ennig a b) else 
    "(Ennig.ennig "^(string_of_int a)^" "^(string_of_int b)^")" ;;
let string_of_il l =
     if List.length(l)<=3 then basic_string_of_il l else 
     let temp1 = Listennou.decompose_into_connected_components l in 
     let draft =String.concat "@" (Image.image string_of_interval temp1) in 
    if List.length(temp1)<2 then draft else "("^draft^")";;       
let string_of_ill l = "["^(String.concat ";" (Image.image string_of_il l))^"]" ;;

module Case = struct

type t = 
   Compatible 
 | Decomposable of int list list
 | Ramifiable of int list ;;

let level = function 
  Compatible -> 1
| Decomposable _ -> 2 
| Ramifiable _ -> 3 ;;

let order = ((fun case1 case2 ->
   let trial1 = Total_ordering.for_integers (level case1) (level case2) in 
   if trial1 <> Total_ordering_result_t.Equal then trial1 else  
   Total_ordering.standard case1 case2  
) : t Total_ordering_t.t);;
   
let current_insertion_level = "three" ;;

let one_command level (x,case,sol) = 
  let s_x=   string_of_il x 
  and lvl = string_of_int level in 
  match case with
  Compatible -> "g_add_compatible "^lvl^" "^s_x^" ;;"
 |Decomposable(ll) -> "g_add_decomposable "^lvl^" "^s_x^" "^(string_of_ill ll)^" "^(string_of_il sol)^" ;;"
 |Ramifiable(obs) -> "g_add_ramification "^lvl^" "^s_x^" "^(string_of_il obs)^" ;;" ;;

let commands_for_one_block (lvl,l)=
  (String.concat "\n" (Image.image (one_command lvl) l))^"\n\n\n"  ;;

let show_commands ll=
  let msg = "\n\n\n"^(String.concat "\n\n" 
  (Image.image commands_for_one_block  ll))^"\n\n\n" in 
  print_string msg ;;


end ;;

let i_order = Total_ordering.for_integers ;;
let i_does_not_intersect = Ordered.does_not_intersect i_order ;;
let i_fold_intersect = Ordered.fold_intersect i_order ;;
let i_fold_merge = Ordered.fold_merge i_order ;;
let i_intersects = Ordered.intersects i_order ;;
let i_mem = Ordered.mem i_order ;;
let i_merge = Ordered.merge i_order ;;
let i_is_included_in = Ordered.is_included_in i_order ;;
let i_outsert = Ordered.outsert i_order ;;

let il_order = Total_ordering.silex_for_intlists ;;
let il_fold_merge = Ordered.fold_merge il_order ;;
let il_mem = Ordered.mem il_order ;;
let il_merge = Ordered.merge il_order ;;
let il_sort = Ordered.safe_set il_order ;;

let small_n = 100 ;;

exception Nondisjoint_parts of (int list) * (int list) ;;
exception Bad_merger of (int list) * (int list) ;;

let check_for_partition x parts =
  let temp1 = Uple.list_of_pairs parts in 
  match Option.seek (fun (part1,part2)->i_intersects part1 part2) temp1 with
  Some(part3,part4) -> raise(Nondisjoint_parts(part3,part4))
  |None ->
  let merger = i_fold_merge parts in 
  if merger <> x
  then raise(Bad_merger (merger,x)) 
  else ();;  


module type HAS_MEASURE = sig 
  val current_width : int
  val impatient_measure : int list -> int list 
  val analize : int list list -> (int * (int list * Case.t * int list) list) list
end ;;



module Next_level = functor (Preceding_level:HAS_MEASURE) -> struct

let current_width = (Preceding_level.current_width) + 1 ;; 
let max_width = Sz_max_width_t.MW current_width ;;
let is_admissible = Sz_preliminaries.test_for_admissibility max_width ;;
let old_measure = Preceding_level.impatient_measure ;;
let old_analize = Preceding_level.analize ;;

exception Incorrect_solution of (int list) * (int list) ;;

let check_solution sol_x x =
    if (i_is_included_in sol_x x) && (is_admissible sol_x)
    then ()
    else raise(Incorrect_solution(sol_x,x)) ;;   

let current_obstructions x = 
  let temp0 = Image.image (fun t->[t-2*current_width;t-current_width;t]) x in 
  List.filter (fun obstruction -> i_is_included_in obstruction x) temp0 ;;

let latest_obstruction x = 
  let temp0 = List.rev_map (fun t->[t-2*current_width;t-current_width;t]) x in 
  Listennou.force_find (fun obstruction -> i_is_included_in obstruction x) temp0 ;;

let hashtbl_for_patient_measure = 
  (( Hashtbl.create 100 ):  
   (int list, int list) Hashtbl.t );;

let force_compute_patient_measure old_f x=  
   let candidate = old_measure x in 
   if is_admissible candidate 
   then candidate 
   else 
  let latest_obs = latest_obstruction x  in 
  let temp1 = Image.image (fun t->old_f (i_outsert t x)) latest_obs in 
  let (_,temp2) = Max.maximize_it_with_care List.length temp1 in 
  let temp3 = il_sort temp2 in 
  List.hd temp3 ;;
    
let careful_translate d x = if d=0 then x else Image.image (fun t->t+d) x ;;

let translation_decomposition x = match x with 
  [] -> (0, [])
  | first_elt::others -> 
      let d = (first_elt-1) in 
      (d,careful_translate (-d) x) ;;


let rec patient_measure x = 
    let (d,tx) = translation_decomposition x in 
    match Hashtbl.find_opt hashtbl_for_patient_measure tx with
     Some old_answer -> careful_translate d old_answer 
    |None ->
       let answer = force_compute_patient_measure patient_measure tx in 
       let _ = Hashtbl.add hashtbl_for_patient_measure tx answer in 
       careful_translate d answer ;;  


let hashtbl_for_impatient_measure = 
        (( Hashtbl.create 100 ):  
         (int list, int list) Hashtbl.t );;


let impatient_measure_opt x = 
  let (d,tx) = translation_decomposition x in 
  match Hashtbl.find_opt hashtbl_for_impatient_measure tx with
    Some old_answer -> Some(careful_translate d old_answer) 
    |None -> None ;;  

exception Impatient_measure_exn of (int list) ;;

let impatient_measure x = match impatient_measure_opt x with 
  None -> raise(Impatient_measure_exn(x))  
 |Some answer->answer;;

let add_to_both x y = 
  (
    Hashtbl.add hashtbl_for_patient_measure x y ;
    Hashtbl.add hashtbl_for_impatient_measure x y
  ) ;;

exception Add_compatible_exn of (int list) * (int list);;

let add_compatible x=
  let candidate = old_measure x in 
  if not(is_admissible candidate) 
  then raise(Add_compatible_exn(x,candidate)) 
  else add_to_both x candidate ;;

exception Add_decomposable_exn of (int list) * ((int list) list);;

let add_decomposable x parts sol_for_x = 
   let _ = check_for_partition x parts in 
   let _ = check_solution sol_for_x x in 
   let combined_length = Basic.fold_sum(Image.image (fun part->
    List.length(impatient_measure part)) parts) in 
   if (List.length(sol_for_x)<>combined_length)
   then raise(Add_decomposable_exn(sol_for_x,parts)) 
   else add_to_both x sol_for_x ;; 
  
let add_ramification x obs =
  let temp1 = Image.image (fun t-> impatient_measure (i_outsert t x)) obs in 
  let (_,temp2) = Max.maximize_it_with_care List.length temp1 in 
  let temp3 = il_sort temp2 in 
  let answer = List.hd temp3 in 
  add_to_both x answer ;;  
  


let start_decomposing  x = 
  let n = List.length x 
  and m =List.length (patient_measure x) in 
  Option.seek (
     fun k->
       let (rleft,right) = Listennou.big_rht k x in
       let left = List.rev rleft in 
       let size_left  = List.length(patient_measure left)
       and size_right = List.length(patient_measure right) in 
       m = size_left + size_right  
  ) (Ennig.ennig 1 (n-1)) ;;


let full_decomposition x =
   let rec tempf = (fun (treated,to_be_treated)->
      match to_be_treated with 
      [] -> List.rev treated 
      | part :: other_parts ->
        match  start_decomposing part with 
         None -> tempf(part::treated,other_parts)
         | Some k ->
          let (rleft,right) = Listennou.big_rht k part in
          let left = List.rev rleft in 
          tempf(left::treated,right::other_parts)  
    ) in 
    tempf([],[x]) ;;

let latest_extra extra_obstructions = 
  let m = List.length (List.hd extra_obstructions) in 
  let temp1 = List.filter (fun z -> List.length z = m) extra_obstructions in 
  let n = Max.list(List.flatten temp1) in 
  let reverter = (fun z->List.rev_map (fun t->n+1-t) z) in 
  let temp2 = il_sort(Image.image reverter temp1) in 
  reverter(List.hd temp2) ;;

let extended_old_measure = Memoized.recursive( fun old_f (x,extra_obstructions) ->
   if extra_obstructions = [] 
   then old_measure x 
   else
    let latest_obs = latest_extra extra_obstructions in 
    let temp1 = Image.image (fun t->old_f (i_outsert t x,
     il_sort(List.filter (fun z->not(i_mem t z)) extra_obstructions)
    )) latest_obs in 
    let (_,temp2) = Max.maximize_it_with_care List.length temp1 in 
    let temp3 = il_sort temp2 in 
    List.hd temp3    
) ;;  
       
exception Compute_ramification_exn of int list ;;

let compute_ramification x=
  let obses = current_obstructions x in 
  let n = List.length obses and m=List.length(patient_measure x) in 
  match Option.seek (
    fun k->
       let limited_obses = Listennou.big_head k obses in 
       List.length(extended_old_measure(x,limited_obses))<=m
  )(Ennig.ennig 1 n) with 
  Some k0 -> List.nth obses (k0-1)
  | None -> raise (Compute_ramification_exn(x)) ;;

let first_analysis x= 
  let candidate = old_measure x in 
  if is_admissible candidate then Case.Compatible else 
  let dec_for_x=full_decomposition  x in 
  if dec_for_x<>[x] then Case.Decomposable(dec_for_x) else
    Case.Ramifiable(compute_ramification x) 
;;

let order_for_analysis_pairs =
    Total_ordering.product il_order  Case.order  ;;

exception Pusher_for_analysis_exn ;;    

let pusher_for_analysis (treated,to_be_treated) =
  match to_be_treated with 
  [] -> raise(Pusher_for_analysis_exn)
  |x1 :: other_xs ->
    let y1 = first_analysis x1 in 
    let possible_new_work = (
        match y1 with 
           Case.Compatible -> []
          |Case.Decomposable(parts)-> parts 
          |Case.Ramifiable(breakers) -> List.rev_map (fun t->i_outsert t x1) breakers
        ) in 
    let new_work = List.filter (
           fun z -> impatient_measure_opt z=None  
        ) possible_new_work in 
  (Ordered.insert order_for_analysis_pairs (x1,y1) treated,new_work@other_xs) ;;

let rec helper_for_analysis (treated,to_be_treated) =
  match to_be_treated with 
   [] -> treated 
  |x1 :: other_xs ->
    let next = pusher_for_analysis (treated,to_be_treated) in 
    helper_for_analysis next ;;

let analize lx = 
   let data_for_current_level =
   Image.image (fun (a,b)->(a,b,patient_measure a)) 
    (helper_for_analysis ([],lx)) in
   if data_for_current_level = [] then [] else  
   let related_to_preceding_level = Option.filter_and_unpack (
      fun (x,case,sol) -> 
        if case = Case.Compatible then Some(x) else None
   ) data_for_current_level in 
   (current_width,data_for_current_level) :: 
   (old_analize related_to_preceding_level);;

end ;;

module Level_one = struct 

  let current_width = 1 ;;

  let impatient_measure x =  
    let temp1 = Listennou.decompose_into_connected_components x in 
    let temp2 = Image.image (
       fun (a,b) -> List.filter (fun x->
         ((x-a) mod 3)<2
        ) (Ennig.ennig a b)) temp1 in 
    List.flatten temp2 ;;      
  
  let analize lx = [] ;;

  end ;;  

module Level_two = Next_level (Level_one) ;;  
module Level_three = Next_level (Level_two) ;;  
  
exception Unknown_depth ;;

let g_add_compatible = function 
   2 -> Level_two.add_compatible 
  |3 -> Level_three.add_compatible  
  |_ -> raise Unknown_depth ;;

let g_add_ramification = function 
  2 -> Level_two.add_ramification 
 |3 -> Level_three.add_ramification  
 |_ -> raise Unknown_depth ;;

let g_add_decomposable = function 
   2 -> Level_two.add_decomposable 
  |3 -> Level_three.add_decomposable  
  |_ -> raise Unknown_depth ;;

for k = 1 to small_n do g_add_compatible 2 (Ennig.ennig 1 k) done ;;
  
for k = 1 to 6 do g_add_compatible 3 (Ennig.ennig 1 k) done ;;
(*

This line triggers an incompletely displayed exception in the toplevel : 
g_add_compatible 3 [1; 2; 3; 5; 6; 7] ;;
*)

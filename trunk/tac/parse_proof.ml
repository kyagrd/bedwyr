(* Build/use requires ocaml-xmllight:
 * ocamlc -I +xml-light xml-light.cma parse_proof.ml -o parse_proof
 * cat /tmp/three.xml | ./parse_proof > /tmp/threebis.xml
 *)

(** Our XML format:
  * <rule>
  *   <name>string</name>
  *   <sequent>
  *     <level>int</level>
  *     <lhs>
  *       <formula polarity=".." mark="..">string</formula>
  *       ...
  *     </lhs>
  *     <rhs>...</rhs>
  *   </sequent>
  *   <formula>...</formula>
  *   <bound>string</bound> (bound variables)
  *   <sub>
  *     other <rule>
  *   </sub>
  * </rule> *)

type formula = bool*Xml.xml

let fail expected x = failwith ("Not a "^expected^":\n"^Xml.to_string x)

let parse_formula = function
  | Xml.Element ("formula",attr,_) as x ->
      (try List.assoc "mark" attr = "focused" with Not_found -> false), x
  | x -> fail "formula" x

let parse_side = List.map parse_formula

type rule = {
  name : string ;
  level : int ;
  lhs : formula list ;
  rhs : formula list ;
  active : formula ;
  bound : string ;
  sub : rule list
}

let rec parse_rule = function
  | Xml.Element ("rule",[],
      [ Xml.Element ("name",[],[Xml.PCData name]) ;
        Xml.Element ("sequent",[],[
          Xml.Element ("level",[],[Xml.PCData level]);
          Xml.Element ("lhs",[],lhs);
          Xml.Element ("rhs",[],rhs)
        ]) ;
        formula ;
        Xml.Element ("bound",[],bound) ;
        Xml.Element ("sub",[],sub) ]) ->
      { name = name ;
        level = int_of_string level ;
        lhs = parse_side lhs ;
        rhs = parse_side rhs ;
        active = parse_formula formula ;
        bound = (match bound with [Xml.PCData s] -> s | _ -> "") ;
        sub = parse_rules sub }
  | x -> fail "rule" x
and parse_rules l = List.map parse_rule l

let xml = Xml.parse_in stdin

let proof = parse_rule xml

let print_leafs = false

let rec outline same_foc = function
  | Xml.Element ("rule",[],
      [ Xml.Element ("name",[],[Xml.PCData name]) ;
        Xml.Element ("sequent",[],[
          Xml.Element ("level",[],[Xml.PCData level]);
          Xml.Element ("lhs",[],lhs);
          Xml.Element ("rhs",[],rhs)
        ]) ;
        formula ;
        Xml.Element ("bound",[],bound) ;
        Xml.Element ("sub",[],sub) ]) as rule ->
      let formula = parse_formula formula in
        if print_leafs && sub = [] then
          [rule]
        else if name <> "induction" && same_foc (fst formula) then
          List.concat (List.map (outline same_foc) sub)
        else
          [ Xml.Element
              ("rule",[],
               [ Xml.Element ("name",[],[Xml.PCData name]) ;
                 Xml.Element ("sequent",[],[
                   Xml.Element ("level",[],[Xml.PCData level]);
                   Xml.Element ("lhs",[],lhs);
                   Xml.Element ("rhs",[],rhs)
                 ]) ;
                 snd formula ;
                 Xml.Element ("bound",[],bound) ;
                 Xml.Element
                   ("sub",[],
                    List.concat (List.map
                                   (outline ((=) (fst formula)))
                                   sub)) ])]
  | x -> fail "rule" x

let () =
  let x = outline (fun _ -> false) xml in
    assert (List.length x = 1) ;
    print_string (Xml.to_string_fmt (List.hd x))

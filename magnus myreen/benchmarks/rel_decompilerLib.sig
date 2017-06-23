signature rel_decompilerLib =
sig

    include Abbrev

    val fast_decompile    : string -> term quotation -> thm list * thm

    val quote_to_strings  : term quotation -> string list

end





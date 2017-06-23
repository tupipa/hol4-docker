signature arm_relLib =
sig

    include Abbrev

    val arm_spec             : string -> (thm * int * int option) *
                                         (thm * int * int option) option

    val arm_enc              : string -> string

    val swap_primes          : term -> term
    val SWAP_PRIMES_RULE     : thm -> thm

end

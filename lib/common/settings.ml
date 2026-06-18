type 'a setting = 'a ref

module ReceiveTypingStrategy = struct
    type t = Strict | Interface | Nothing
    
    let enum = [("strict", Strict);
                ("interface", Interface);
                ("none", Nothing)]  
end

let verbose = ref false
let debug = ref false
let benchmark = ref (-1)
let receive_typing_strategy = ref ReceiveTypingStrategy.Interface
let liberal_datatypes = ref false
let disable_quasilinearity = ref false
let join_not_combine = ref false
let show_ir = ref true
let show_ref_counting = ref false
let eval = ref false

let set : 'a setting -> 'a -> unit = fun setting value ->
    setting := value

let get : 'a setting -> 'a = fun setting -> !setting

let if_verbose f =
    if get verbose then f () else ()

let if_debug f =
    if get debug then f () else ()

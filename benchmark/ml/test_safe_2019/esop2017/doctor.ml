(***********************************************************************)
(*                                                                     *)
(*                        Caml examples                                *)
(*                                                                     *)
(*            Pierre Weis                                              *)
(*                                                                     *)
(*                        INRIA Rocquencourt                           *)
(*                                                                     *)
(*  Copyright (c) 1994-2011, INRIA                                     *)
(*  All rights reserved.                                               *)
(*                                                                     *)
(*  Distributed under the BSD license.                                 *)
(*                                                                     *)
(***********************************************************************)

(* $Id: doctor.ml,v 1.2 2011-08-08 19:31:17 weis Exp $ *)

exception Found;;

let is_character_in_string str ch =
    try
      for i = 0 to String.length str - 1 do
        if str.[i] = ch then raise Found
      done;
      false
    with Found -> true
;;

let rec member elem = function
  | [] -> false
  | x :: rest -> x = elem || member elem rest
;;

(* Note: for pedagogical purpose this exception is different from the
   standard exception Not_found *)
exception Not_Found;;

let rec associate_of x = function
  | [] -> raise Not_Found
  | (key, value) :: l ->
      if x = key then value else associate_of x l;;

let rec associate_in_list key = function
  | [] -> raise Not_Found
  | (list_of_keys, value) :: rest ->
      if member key list_of_keys then value
      else associate_in_list key rest
;;

let rec associate_of_an_element_of list_of_keys association_list =
  match list_of_keys with
  | [] -> raise Not_Found
  | key :: rest ->
     try
       associate_in_list key association_list
     with Not_Found ->
       associate_of_an_element_of rest association_list
;;

let lowercase_all str =
  let lowercase_of ch =
    if int_of_char ch >= 65 && int_of_char ch <= 90
    then char_of_int (int_of_char ch + 32)
    else ch
  in
  let string_in_lowercase =
    String.create (String.length str) in
  for i = 0 to String.length str - 1 do
    string_in_lowercase.[i] <- lowercase_of str.[i]
  done;
  string_in_lowercase
;;

let simplify_word word =
  let simplifications =
    [("à","a"); ("ç","c"); ("é","e"); ("è","e"); ("ê","e"); ("ù","u");
     ("a`","a"); ("e'","e"); ("e`", "e"); ("e^","e"); ("u`","u");
     ("qu'", ""); ("l'", ""); ("d'", "");
     ("n't", "nt"); ("'s", "s"); ("'m", "m"); ("'d", "d"); ("'ve", "ve")]
  in
  let new_word = String.create (String.length word) in
  let i = ref 0 and j = ref 0 in
  let rec search_translation = function
  | [] -> raise Not_Found
  | (original, translation) :: rest ->
      let length = String.length original in
      if !i + length <= String.length word
       && String.sub word !i length = original
      then (length, translation)
      else search_translation rest in
  while !i < String.length word do
    try
      let (length, translation) =
        search_translation simplifications in
      String.blit translation 0 new_word !j
                  (String.length translation);
      i := !i + length;
      j := !j + String.length translation
    with Not_Found ->
      new_word.[!j] <- word.[!i];
      i := !i + 1;
      j := !j + 1
  done;
  String.sub new_word 0 !j
;;

let divide_in_words str =
  let substring s start finish =
    String.sub s start (finish - start + 1)
  in
  let words = ref [] in
  let j = ref (String.length str - 1) in
  let add_word i j =
      if i <= j then
      words := simplify_word (substring str i j) :: !words in
  for i =  String.length str - 1 downto 0 do
    match str.[i] with
    | (' ' | '\n' | '.' | ',' | ';' | '-' | '!' | '?') ->
       add_word (i + 1) !j; j := i - 1
    | _ -> ()
 done;
 add_word 0 !j;   (* extraction of last word *)
 !words
;;


let price_to_pay = ref 0;;

let patient_response = ref "";;

let rec synonym_of_phrase = function
  | ["how"] -> ["what"]
  | ["of"; "course"] -> ["yes"]
  | "certain" :: "that" :: rest -> synonym_of_phrase rest
  | "not" :: "at" :: "all" :: _ -> ["no"]
  | phrase -> phrase
;;

exception Finished;;

let answer_patient () =
  let message s = print_string s; print_newline () in
  let is_goodbye ph = (ph = ["so"; "long"]) || (ph = ["bye"]) ||
                        (ph = ["goodbye"]) || (ph = ["see you later"])
  in
  let answers_to_simple_phrases =
  [([],
    [|"Do you want to change the subject?";
      "Go on";
      "Go on, I'm interested";
      "I'm listening";
      "Do you have nothing else to say?";
      "Go on, please";
      "Is that all you have to say?";
      "I still don't know enough about you; go on"|]);
   (["what"],
    [|"Excuse me, I was thinking of something else, go on";
      "Think about it";
      "Let's change the subject, please";
      "I think I'm making sense";
      "Well, it seemed clear enough to me";
      "Communication is difficult, isn't it?";
      "Ah, men!  They don't understand anything!";
      "Stop asking questions";
      "Wouldn't you have problems understanding me?"|]);
   (["no"],
    [|"That was abrupt";
      "Could you be more specific?";
      "I'm taking note: it's no";
      "But still?";
      "The answer isn't so simple, is it?";
      "You are really quite sure of yourself";
      "Doesn't it occur to you to doubt yourself?";
      "Don't always answer yes or no";
      "Yes/no syndrome.  Explain yourself, for crying out loud!";
      "At least you don't suffer from verbal diarrhea";
      "How can you be so sure of yourself?"|]);
   (["yes"],
    [|"That's a bit abrupt";
      "Give me more detail";
      "Could you be more specific?";
      "I would like to understand why";
      "The answer isn't so simple, is it?";
      "That's solid and sincere at least";
      "That doesn't really tell me any more, explain to me why.";
      "Are you sure?";
      "Be less brief: elaborate";
      "Any more closemouthed and you'd have to be dead";
      "If you don't explain to me better, how am I to understand you?";
      "Don't always answer yes or no";
      "And the rest is history";
      "And for what reasons?"|]);
   (["and"; "then"; "well"; "so"],
    [|"Well, explain to me";
      "Don't be so aggressive";
      "Well, I would like to have more information about it";
      "Zorro is here";
      "Well, well, explain yourself!";
      "That was a test to see if you were following"|]);
   (["again"],
    [|"We can change the subject if you like?";
      "The boil must be thoroughly lanced!";
      "Important things need to be said!";
      "I'm more stubborn than you are!";
      "Do you think I'm rambling?";
      "Just say right out that I'm senile!"|])
  ]
  in
  let answers_to_small_words =
  [(["isnt"],
    [|"Not at all?";
      "Really not?";
      "Why not?"|]);
   (["never"],
    [|"Never say ``never''";
      "Never seems to me a bit strong, don't you think?";
      "Never?"|]);
   (["no"],
    [|"Are you sure of that?";
      "Why not?";
      "What would you say in the opposite case?";
      "A case could be made for that opinion";
      "Well, at least I know your opinion about it"|]);
   (["nothing"],
    [|"Nothing at all?";
      "Why not?";
      "What would you say in the opposite case?";
      "A case could be made for that opinion";
      "Well, at least I know your opinion about it";
      "Not even a little bit?";
      "Nothing is a bit of an exaggeration, don't you think?"|]);
    (["why"],
     [|"Because";
      "I don't answer questions from patients";
      "If you don't know, it's not for me to tell you";
      "No one can answer this question";
      "Do you think a machine can answer that?";
      "That would take too long to explain";
      "I know very well why, but you wouldn't understand";
      "It's hard to say"|]);
    (["none"],
     [|"Really none?";
       "Not in the least?";
       "Do you wish it were otherwise?";
       "That's a new fact for me"|]);
    (["not"],
     [|"That seems a little negative to me";
       "Really?";
       "Why so?";
       "I wouldn't have doubted it";
       "Difficult";
       "I'm used to hearing that";
       "Are you troubled at this point?";
       "You shouldn't talk like that"|]);
    (["know"; "knows"; "knowing"; "knew"; "known"],
     [|"Knowledge is a rare commodity";
       "Are you certain of knowing that?";
       "Isn't there still some doubt?";
       "I wouldn't be able to say as much";
       "Difficult to admit";
       "Are you so sure of that?"|]);
    (["yes"],
     [|"Are you sure of that?";
       "You're really sure of yourself";
       "That didn't seem obvious to me";
       "Still, I would have thought the contrary";
       "That's interesting, go on";
       "What an unqualified affirmation";
       "Very well";
       "What a declaration!";
       "Good"|]);
    (["what";"how"],
     [|"That's for you to tell me";
       "Hard to say";
       "Think, you'll understand";
       "The answer is within you"|]);
    (["thank";"thanks";"thanking"],
     [|"Don't thank me";
       "I'm here to help you";
       "Well well, go on";
       "It's all natural";
       "It was really easy"|])
  ]
  in
  let answers_to_questions =
  [| "I'm the one asking the questions";
     "I'm not here to answer your questions";
     "A very interesting question, but what do you think about it?";
     "What a question!";
     "Why are you asking me this question?";
     "You know very well";
     "The answer is unimportant";
     "My telling you would gain you nothing";
     "A psychoanalyst does not have the right to answer these questions";
     "I don't have the right to answer you";
     "I am forbidden to tell you";
     "You wouldn't understand";
     "Let me not answer that";
     "Let me think.  Can you restate the question?";
     "I'm not sure I've correctly understood the question";
     "I don't know";
     "Think a little";
     "It's obvious to everyone but you; think about it!";
     "It is for you to find the answer";
     "Look deep within yourself, indeed you know"|]
  in
  let restarters =
  [| "Tell me a little about yourself";
     "Are you married?";
     "Do you have children?";
     "Tell me about your environment";
     "Do you like life?";
     "Do you like this way of communicating?";
     "Let's talk about your family.";
     "Tell me some more about yourself";
     "What do you think of computers?";
     "What shall we talk about now?";
     "Do you have a lot of friends?";
     "Do you have serious problems?";
     "Tell me about your problems";
     "Do you have strange dreams?";
     "Do you often have nightmares?";
     "What do you think of love?";
     "What do you think of sexuality?";
     "What are your hobbies?";
     "What interests you in life?";
     "What do you think of life in general?"|]
  in
  let answers_to_interesting_words =
  [(["fear"; "fears"; "feared";
     "fright"; "frightful"; "frightening"; "frightened";
     "scare"; "scares"; "scared"; "afraid"],
    [|"Talk to me about your fears";
      "Are you often afraid?";
      "Do you have unexplained fears, nightmares?"|]);
   (["dead"; "death"; "die"; "died"; "dying"; "dies"],
    [|"I feel very sorry for you";
      "Death is a very serious subject";
      "You have to try to absorb it";
      "That's unfortunate";
      "Try not to think about it any more"|]);
   (["unhappy"; "problem"; "problems"; "suffering";
     "unlucky"; "troubled"; "unfortunate"],
    [|"Tell me your problems";
      "Which troubles are yours?";
      "Do you really have reasons to feel sorry for yourself?";
      "Happiness exists too you know."|]);
   (["misfortune"; "unhappiness"; "trouble"],
    [|"Trouble is a bit of an exaggeration, isn't it?";
      "Trouble is a relative notion.  What do you mean by trouble?";
      "Joy, sorrow, that's all I hear about.  Go on."|]);
   (["boredom"; "bore"; "boring"; "bored"; "bores"],
    [|"Boredom, that depends on you";
      "Am I boring you?";
      "I'm sorry for you";
      "That's too bad for you"|]);
   (["annoyances"; "nuisances"; "worries"; "troubles"],
    [|"Troubles are often ephemeral";
      "Everything can't always be rosy, can it?";
      "How sad, don't you think?";
      "Is it really very serious?"|]);
   (["comptuer"],
    [| "I guess you mean computer"|]);
   (["computer"; "computers"; "machine"; "machines"],
    [|"Do you know computers well?";
      "Let's change the subject, that doesn't interest me";
      "Ah, machines!";
      "Machines are so stupid!";
      "I know computers well, and I avoid having anything to do with them!";
      "You know, I'm a machine myself..."|]);
   (["programming"; "programmer"; "programmers"; "software"],
    [|"What a beautiful occupation, to deal with computers";
      "Ah programming!";
      "Programming is a difficult job";
      "Programming is difficult, isn't it?";
      "Do you really like computers?";
      "I've been told you aren't madly in love with computers"|]);
   (["family"],
    [|"Do you have brothers and sisters?";
      "Tell me about your father";
      "Tell me about your mother";
      "That's what really interests me";
      "Tell me more about your family";
      "The family is often complicated"|]);
   (["father"],
    [|"Do you look like your father?";
      "Tell me some more about your father";
      "And your mother?";
      "Your father?"|]);
   (["mother"],
    [|"Do you look like your mother or your father?";
      "Tell me some more about your mother";
      "And your father?";
      "Your mother?"|]);
   (["friend"; "friends"; "buddy"; "buddies"],
    [|"Do you have a lot of friends?";
      "How did you meet?";
      "How does that happen with your friends?";
      "Do you often have arguments with your friends?";
      "Friends?";
      "Boyfriends? Girlfriends?";
      "How long have you known each other?"|]);
   (["hate"; "hates"; "detest"; "detests"],
    [|"Is it reasonable to hate at this point?";
      "Isn't that word a bit strong?"|]);
   (["husband"],
    [|"Have you been together long?";
      "How did you meet him?";
      "Do you think one must be faithful to one's husband?" |]);
   (["love"],
    [|"And obsession, what do you think about that?";
      "Love is complicated, isn't it?";
      "Love, love, are you really familiar with it?";
      "Have you already known love?";
      "Love, how did you come upon it?"|]);
   (["money"],
    [|"Not having money is a pain unlike any other";
      "Do you have money problems?";
      "Money has many connotations, go on talking about it";
      "Do you like money very much?";
      "Are you afraid of not having enough money?"|]);
   (["caml"; "ocaml"],
    [|"You mean Camel cigarettes?";
      "I've heard of this remarkable OCaml language";
      "Everything you say may be used against you";
      "Without OCaml I wouldn't be here; so I refuse to talk about it";
      "In my opinion, OCaml is unequaled";
      "Since it's a free language, it undoubtedly isn't too bad";
      "OCaml is powerful, but what syntax, eh?";
      "OCaml, is that a standard language?";
      "As its name indicates, it's an object oriented language, right?";
      "OCaml is an artificial intelligence language, right?";
      "Don't you think the syntax should be revised?";
      "I state categorically: OCaml is a very abstract language!"
    |]
   );
   (["sml"],
    [|"Don't provoke me please";
      "Don't talk to me about dinosaurs";
      "SML you say?";
      "I've never heard of SML, what is it?";
      "It would be necessary to know, is it ML or not?"|]);
   (["language"; "languages"],
    [|"Do you mean programming language?";
      "I only know the OCaml language";
      "Do you know the OCaml language well?";
      "There's no safety outside of Ocaml, right?";
      "In my opinion, OCaml is without equal";
      "Yes, it's powerful, but what a syntax!";
      "And syntax problems?"
    |]
   );
   (["program"; "programs"],
    [|"You're talking about computer programs?";
      "There are often bugs in your programs, right?";
      "Do you really know programming?";
      "Your programs could be written more naturally in OCaml";
      "In my opinion, programming is easy, don't you think?";
      "Do you have problems with your programs?"
    |]
   );
   (["camel"; "camels"],
    [|"The camel is a charming animal of great dignity, don't you think?";
      "The camel is my favorite animal, isn't it yours?";
      "Certainly the camel is a bit of a difficult character, but there are \
      some charming ones, isn't that so?";
      "A camel with two humps or a dromedary?";
      "What else do you have to say about camels?"|]);
   (["love"],
    [|"Very much?";
      "Without the slightest reservation?";
      "Why this attraction?";
      "How to explain this feeling?";
      "Can one truly love?";
      "To love or not to love, is that really the question?"|]);
   (["sex"],
    [|"I'm not personally concerned";
      "That would seem interesting!";
      "I've been told sex is important to humans";
      "Sex, okay, but love?";
      "Have you heard of AIDS?"|]);
   (["nightmare"; "nightmares"; "dream"; "dreams"],
    [|"I have a hard time understanding; I never dream!";
      "Your nocturnal activities interest me.  Go on";
      "That seems strange to me!";
      "Do nightmares wake you up at night?";
      "Do you have insomnia?";
      "Do you have a lot of nightmares?";
      "Do you often have strange dreams?";
      "What do you think of hypnosis?"|]);
   (["anxious"; "anxiety"; "worry"; "worried"; "worrying"; "worries"],
    [|"Anxiety is a true sickness";
      "Those who are anxious often have problems with their environment. \
       Have you noticed?";
      "Worry is true suffering, don't you think?"|]);
   (["stupid"; "idiot"],
    [|"Do you think it's a crime to be stupid?";
      "I have excellent friends who are stupid too";
      "Idiocy is the most widely distributed thing in the world";
      "Don't be stupid either";
      "You yourself, aren't you stupid sometimes?";
      "Don't you think it's sometimes useful to be stupid?"|]);
   (["wife"],
    [|"Have you been together a long time?";
      "How did your meeting take place?"|]);
   (["woman"],
    [|"Do you love this woman?";
      "Is this an ordinary woman?"|]);
   (["bad"; "hard"; "difficult"],
    [|"I feel very sorry for you";
      "Are you sure you're being objective?";
      "I can try to help you";
      "Is that all you meant to tell me?";
      "Is that why you've come to see me?"|]);
   (["tired"],
    [|"Being tired is not a disease";
      "When you're tired shouldn't you rest?";
      "I'm a machine; I never get tired";
      "What do you think about fatigue in general?";
      "Why do you think it's worth the trouble of tiring yourself out?";
      "Tired people often are tired by their own doing, don't you think?"|]);
   (["you"],
    [|"Let's not talk about me";
      "Let's talk about you, that's more important";
      "If it were said of you?";
      "Me, I'm only a machine...";
      "Me?";
      "Excuse me";
      "Don't hold it against me if I interrogate you.  Go on";
      "You don't really think so?"|])
  ]
  in
  let choice_from v = v.(Random.int (Array.length v)) in
  let r = lowercase_all !patient_response in
  let phrase = divide_in_words r in
  if is_goodbye phrase then raise Finished else
  let possible_answers =
      try associate_of (synonym_of_phrase phrase)
                     answers_to_simple_phrases
      with Not_Found ->
      try associate_of_an_element_of phrase
          answers_to_interesting_words
      with Not_Found ->
      if is_character_in_string r '?'
      then answers_to_questions
      else try associate_of_an_element_of phrase
               answers_to_small_words
           with Not_Found -> restarters in
  message (choice_from (possible_answers));
  print_newline ()
;;

let camelia () =
  let message s = print_string s; print_newline () in
  let say_goodbye () =
    let choice_from v = v.(Random.int (Array.length v)) in
    let farewells =
    [|"It will be long and difficult, come back and see me often ...";
      "Your case is not simple, and even rather worrying ... Until later?";
      "Simple diagnosis: wihtout a doubt you are paranoid.";
      "With a probability of 92.37234%: polymorphous perversion.";
      "You are suffering from rapidly evolving schizophrenia, DANGER";
      "According to my calculations, your mental health has been compromised.";
      "My final advice: you must not stay that way, take care!"|]
    in
    message "\nThe result of my observations:\n";
    message (choice_from farewells);
    message "\nGoodbye ...\n";
    print_string "You owe me "; print_int !price_to_pay;
    message " dollars. Make out a check to the order of Camelia. Thank you."
  in
  let hello () =
    let message s = print_string s; print_newline () in
    price_to_pay := 30;
    message "\nHello, my name is Camelia.";
    message "\nI'm here to help you resolve your psychological problems.";
    message "Finish by telling me: Goodbye.";
    message "\nLet's get to it.  Tell me about yourself.\n"
  in
  let listen_to_patient () =
    price_to_pay := !price_to_pay + 2;
    print_string ">> ";
    patient_response := read_line ()
  in
  hello ();
  try
   while true do
     listen_to_patient ();
     answer_patient ()
   done
  with Finished -> say_goodbye ()
     | End_of_file | Sys.Break ->
         message "\n\n\nYou could be polite \
                  and say goodbye to me ...\n\n\n";
         say_goodbye ()
;;

let main () =
if !Sys.interactive then () else begin
  Sys.catch_break true;
  camelia ();
  exit 0
end
;;

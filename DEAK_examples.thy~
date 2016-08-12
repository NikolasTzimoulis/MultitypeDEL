theory DEAK_examples
imports Main DEAK_Core_SE DEAK_SE List
begin

lemma "[] \<turnstile>d A \<^sub>F \<^sub>S \<turnstile>\<^sub>S A \<^sub>F \<^sub>S"
apply(rule Id)
done

lemma "[] \<turnstile>d ((A \<^sub>F) \<and>\<^sub>F (A \<^sub>F) )\<^sub>S  \<turnstile>\<^sub>S  ((A \<^sub>F)  \<and>\<^sub>F (A \<^sub>F) )\<^sub>S "   
by (simp add: "derivable.simps")   
                               
lemma "[] \<turnstile>d  (((A \<^sub>F) \<^sub>S)  \<turnstile>\<^sub>S ((A \<^sub>F) \<^sub>S) ) \<Longrightarrow> [] \<turnstile>d ((A \<^sub>F) \<and>\<^sub>F (A \<^sub>F))\<^sub>S  \<turnstile>\<^sub>S  ((A \<^sub>F) \<and>\<^sub>F (A \<^sub>F))\<^sub>S "
by (simp add:"derivable.simps")
            
end                    
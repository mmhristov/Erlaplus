package pcal;

import java.util.List;

/**
 * A class, which saves all the translation results from trans.performTranslation()
 * and some additional information used for the Erlang code generation
 * @author marian.hristov
 *
 */
public class TranslationResult {
	// The translated TLA+ code 
	private List<String> tlaCode = null;
	// The translated Erlang code 
	private List<String> erlangCode = null; 
	
	public TranslationResult(List<String> tla, List<String> erlang) {
		this.tlaCode = tla;
		this.erlangCode = erlang;
	}

	public List<String> getErlangCode() {
		return erlangCode;
	}

	public List<String> getTlaCode() {
		return tlaCode;
	}
}

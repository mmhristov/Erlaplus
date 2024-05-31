package pcal;

import java.util.List;
import java.util.Vector;

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
	private PcalErlangGenResult erlangResult = null;
	
	public TranslationResult(List<String> tla, PcalErlangGenResult erlangResult) {
		this.tlaCode = tla;
		this.erlangResult = erlangResult;
	}

	public Vector<String> getErlangCode() {
		if (erlangResult != null) {
			return erlangResult.getCode();
		}
		return null;
	}

	public List<String> getTlaCode() {
		return tlaCode;
	}
}

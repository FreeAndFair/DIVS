/**
 * 
 */
package model.data.computation.draw;

import java.util.ArrayList;
import java.util.List;

import model.data.computation.ConstituencyResult;
import model.data.computation.PartyResult;
import model.data.computation.ProvinceResult;

/**
 * @author Ólavur Kjølbro
 */
public class StepFiveDraw {

	private int ranking;
	private PartyResult pres;
	private ProvinceResult pr;
	private List<ConstituencyResult> constituencies;

	//@ invariant ranking > 0;
	//@ invariant pres != null;
	//@ invariant pr != null;
	//@ invariant constituencies != null;

	public StepFiveDraw(int ranking, PartyResult pres, ProvinceResult pr) {
		this.ranking = ranking;
		this.pres = pres;
		this.pr = pr;
		this.constituencies = new ArrayList<ConstituencyResult>();
	}

	/**
	 * @return the ranking
	 */
	public int getRanking() {
		return ranking;
	}

	/**
	 * @return the party result
	 */
	public PartyResult getPartyResult() {
		return pres;
	}

	/**
	 * @return the province result
	 */
	public ProvinceResult getProvinceResult() {
		return pr;
	}

	/**
	 * @return the constituencies
	 */
	public List<ConstituencyResult> getConstituencies() {
		return constituencies;
	}
}

package national.data;

import java.io.Serializable;
import national.ElectionConstants;

/**
 * @author Ólavur Kjølbro
 */
public /*@ nullable_by_default @*/ class Party implements Serializable {

	private static final long serialVersionUID = 1L;

	private int party_id;
	private String name, letter;
	private int standing;
	private boolean party_list;
	
	//@ invariant party_id > 0;
	//@ invariant name != null;
	//@ invariant letter != null;
	//@ invariant standing == ElectionConstants.STANDING_BY_DISTRICT || standing == ElectionConstants.STANDING_IN_PARALLEL;
	//@ invariant party_list == true ==> (standing == ElectionConstants.STANDING_BY_DISTRICT);

	/**
	 * @param party_id Party_id in the database
	 * @param name Name of the party
	 * @param letter Party's letter
	 * @param standing How the party 'stands'
	 */
	//@ pre party_id > 0;
	//@ pre standing == ElectionConstants.STANDING_BY_DISTRICT || standing == ElectionConstants.STANDING_IN_PARALLEL;
	public Party(int party_id, /*@ non_null @*/ String name, 
			/*@ non_null @*/ String letter, int standing,
			boolean pl) {
		this.party_id = party_id;
		this.name = name;
		this.letter = letter;
		this.standing = standing;
		this.party_list = pl;
	}
	
	/**
	 * @return The party id of the party (in the database)
	 */
	public /*@ pure @*/ int getPartyId() {
		return party_id;
	}
	
	/**
	 * @return The name of the party
	 */
	public /*@ pure @*/ String getName() {
		return name;
	}
	
	/**
	 * @return The (party) letter of the party
	 */
	public /*@ pure @*/ String getLetter() {
		return letter;
	}

	/**
	 * @return The standing (or principal form) that the party chooses to use
	 */
	public /*@ pure @*/ int getStanding() {
		return standing;
	}

	/**
	 * @return the party_list
	 */
	public /*@ pure @*/ boolean isPartyList() {
		return party_list;
	}

	/**
	 * @return  A string informing about the instance
	 */
	@Override
	public /*@ pure @*/ String toString() {
		@SuppressWarnings("unused")
		int i = ElectionConstants.SEATS_DENMARK; //used to make the import come without a warning
		return "Party - name: "+name+";letter: "+letter+";standing: "+standing+";party_list: "+party_list;
	}

}
# Comma Selection Feature for ILL Right Tensor Rule

## Overview

This document outlines the implementation of a comma selection feature that allows users to specify the Gamma/Delta split when applying the right tensor rule in Intuitionistic Linear Logic (ILL) mode. The feature enables users to click on commas to select where Gamma ends and Delta begins in the context "Gamma, Delta |- A*B".

## Current State Analysis

### Frontend Structure
- **Main files**: `static/js/app.js`, `static/js/proof.js`, `static/js/sequent.js`
- **ILL detection**: Uses `intuitionisticMode` flag in options
- **Rule display**: ILL rules have specific symbols (e.g., `⊗_R` for tensor right)
- **Sequent rendering**: Formulas are rendered in `<li>` elements with comma `<span>` separators
- **Click handling**: Current system handles formula clicks for rule application

### Backend Structure  
- **ILL modules**: `ill_apply_rule.ml`, `ill_rule_request.ml`, `ill_proof.ml`, `ill_sequent.ml`
- **Rule handling**: `ill_rule_request` defines `context_split: int list option` field (already exists!)
- **Tensor rule**: `ILL_Tensor` rule type exists for right tensor application

## Required Changes

### 1. Frontend Changes (`static/js/`)

#### A. Sequent Display Enhancement (`sequent.js`)

1. **Comma Click Detection**
   - Add click handlers to comma `<span>` elements when in ILL mode
   - Only enable comma clicks when right tensor rule is applicable
   - Add visual feedback (highlighting) when comma selection mode is active

2. **Formula Range Selection**
   - Implement formula highlighting system for Gamma selection
   - Track selected Gamma range (from start to selected comma)
   - Clear selection when tensor rule is applied or cancelled

3. **UI State Management**
   - Add comma selection mode flag to sequent options
   - Track which comma was clicked (position in context)
   - Visual indicators for active selection mode

#### B. Rule Application Logic (`proof.js`)

1. **Comma Selection Mode Activation**
   - Check if right tensor rule is applicable before enabling comma clicks
   - Only in ILL mode (`intuitionisticMode = 1`)
   - Only when goal formula is of form `A ⊗ B`

2. **Rule Request Enhancement**
   - Modify tensor rule application to include `context_split` parameter
   - Convert comma position to context split indices
   - Handle edge cases (empty Gamma, full context as Gamma)

3. **Alternative Tensor Application**
   - Direct tensor symbol click assumes empty Gamma (Delta = full context)
   - Preserve existing behavior for non-comma-selection cases

#### C. Visual Feedback System

1. **Comma Highlighting**
   - Clickable commas get visual indication (cursor, hover effects)
   - Selected comma gets distinct styling
   - Only show in ILL mode when tensor rule applicable

2. **Formula Range Highlighting**
   - Highlight all formulas from start to selected comma (Gamma)
   - Remaining formulas visually distinct (Delta)
   - Clear highlighting after rule application

### 2. Backend Changes (`*.ml`)

#### A. Rule Request Processing (`ill_rule_request.ml`)

1. **Context Split Validation**
   - Validate `context_split` indices are within context bounds
   - Handle empty Gamma case (context_split = [])
   - Handle full context as Gamma case

2. **Split Index Conversion**
   - Convert frontend comma position to context split indices
   - Ensure proper range validation and error handling

#### B. Rule Application (`ill_apply_rule.ml`)

1. **Tensor Rule Context Splitting**
   - Implement context division based on `context_split` parameter
   - Create two sub-sequents: `Gamma |- A` and `Delta |- B`  
   - Handle empty context cases gracefully

2. **Sequent Generation**
   - Generate proper premise sequents for tensor rule
   - Maintain correct formula ordering and structure
   - Preserve existing tensor rule behavior when no split specified

#### C. JSON Response Format

1. **Context Split Information**
   - Include split information in rule application response
   - Ensure frontend can reconstruct the split for display
   - Maintain backward compatibility

### 3. Integration Points

#### A. Mode Detection
- Frontend checks `intuitionisticMode` flag before enabling comma clicks
- Backend processes `context_split` only for ILL tensor rules
- Graceful fallback to standard behavior in classical LL mode

#### B. Rule Applicability Check
- Frontend validates tensor rule can be applied before enabling comma selection
- Check goal formula is tensor type (`A ⊗ B`)
- Disable comma clicks when rule not applicable

#### C. Error Handling
- Invalid comma positions should show user-friendly errors
- Backend validation of context splits with clear error messages
- Graceful degradation if comma selection fails

## Implementation Plan

### Phase 1: Backend Foundation
1. Enhance `ill_rule_request.ml` context split processing
2. Implement context splitting logic in `ill_apply_rule.ml`
3. Add proper validation and error handling

### Phase 2: Frontend Core Functionality  
1. Add comma click detection to `sequent.js`
2. Implement formula range highlighting system
3. Integrate with existing rule application flow

### Phase 3: UI/UX Polish
1. Add visual feedback for comma selection mode
2. Implement proper highlighting and selection states
3. Add hover effects and user guidance

### Phase 4: Integration & Testing
1. End-to-end testing of comma selection feature
2. Ensure backward compatibility with existing functionality
3. Test edge cases (empty Gamma, single formula contexts)

## Technical Considerations

### Performance
- Comma click handlers only added when needed (ILL mode + tensor applicable)
- Efficient DOM manipulation for highlighting
- Minimal impact on existing classical LL functionality

### Accessibility
- Keyboard navigation support for comma selection
- Screen reader friendly selection indicators
- Clear visual feedback for selection state

### Browser Compatibility
- Standard DOM event handling (no advanced JS features)
- CSS-based highlighting (cross-browser compatible)
- Graceful degradation for older browsers

## Success Criteria

1. **Functional**: User can click comma to select Gamma/Delta split for right tensor rule
2. **Visual**: Clear indication of selection mode and selected range
3. **Compatible**: No impact on classical LL mode or other ILL rules
4. **Robust**: Proper error handling and edge case management
5. **Intuitive**: Natural user interaction flow with minimal learning curve
import { Breakpoint } from '@mui/material';
export declare const MODAL_TYPES: {
    readonly INFORMATION: "information";
    readonly CONFIRMATION: "confirmation";
    readonly INPUT: "input";
};
export type ModalType = (typeof MODAL_TYPES)[keyof typeof MODAL_TYPES];
export declare const INFORMATION_SUBTYPES: {
    readonly ACKNOWLEDGEMENT: "acknowledgement";
    readonly PROGRESS: "progress";
    readonly PASSIVE: "passive";
};
export declare const CONFIRMATION_SUBTYPES: {
    readonly DEFAULT: "default";
    readonly DESTRUCTIVE: "destructive";
    readonly NESTED: "nested";
};
export declare const INPUT_SUBTYPES: {
    readonly DEFAULT: "default";
    readonly DESTRUCTIVE: "destructive";
};
export type InformationSubtype = (typeof INFORMATION_SUBTYPES)[keyof typeof INFORMATION_SUBTYPES];
export type ConfirmationSubtype = (typeof CONFIRMATION_SUBTYPES)[keyof typeof CONFIRMATION_SUBTYPES];
export type InputSubtype = (typeof INPUT_SUBTYPES)[keyof typeof INPUT_SUBTYPES];
export declare const MODAL_SIZES: {
    readonly SMALL: "small";
    readonly MEDIUM: "medium";
    readonly LARGE: "large";
    readonly EXTRA_LARGE: "extraLarge";
};
export declare const TERTIARY_CTA_TYPES: {
    DEFAULT: string;
    DESTRUCTIVE: string;
};
export type ModalSize = (typeof MODAL_SIZES)[keyof typeof MODAL_SIZES];
type ModalConfig = {
    DISMISSIBLE: 'full' | 'partial';
    ALLOWED_SIZES: ModalSize[];
};
type ModalTypeConfig = {
    [subtype: string]: ModalConfig;
};
export declare const MODAL_CONFIGS: Record<ModalType, ModalTypeConfig>;
export declare const SIZE_TO_MAX_WIDTH: Record<ModalSize, Breakpoint>;
export type SubtypeForType<T extends ModalType> = T extends typeof MODAL_TYPES.INFORMATION ? InformationSubtype : T extends typeof MODAL_TYPES.CONFIRMATION ? ConfirmationSubtype : T extends typeof MODAL_TYPES.INPUT ? InputSubtype : never;
export declare const MODAL_SIZE_VS_CLASS_NAMES: {
    small: string;
    medium: string;
    large: string;
    extraLarge: string;
};
export {};
//# sourceMappingURL=viDialog.types.d.ts.map